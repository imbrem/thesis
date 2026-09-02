#!/usr/bin/env python3
# pyright: basic
"""Thesis status queries via Typst.

Subcommands query Typst metadata (TODOs, chapters, etc.) and render
results to the terminal or as JSON.
"""

from __future__ import annotations

import argparse
from collections import Counter
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_ENTRY = "thesis/main.typ"
EDITORIAL_QUEUE = REPO_ROOT / "notes/editorial-queue.json"


# --- Typst helpers ---

def typst_query(entry: str, selector: str, *, field: str | None = "value") -> list[object]:
    """Run `typst query` and return the parsed JSON list."""
    command = ["typst", "query", "--root", str(REPO_ROOT), entry, selector]
    if field is not None:
        command.extend(["--field", field])
    result = subprocess.run(
        command,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        print(result.stderr, file=sys.stderr, end="")
        sys.exit(result.returncode)
    return json.loads(result.stdout)


def render(node: object, *, ansi: bool = False) -> str:
    """Recursively render a Typst content node to text."""
    if isinstance(node, str):
        return node
    if isinstance(node, list):
        return "".join(render(n, ansi=ansi) for n in node)
    if not isinstance(node, dict):
        return ""
    func = node.get("func")
    if func == "text":
        text = node.get("text")
        return text if isinstance(text, str) else ""
    if func == "space":
        return " "
    if func == "linebreak":
        return "\n"
    if func == "strong":
        inner = render(node["body"], ansi=ansi)
        return f"\033[1m{inner}\033[0m" if ansi else inner
    if func == "emph":
        inner = render(node["body"], ansi=ansi)
        return f"\033[3m{inner}\033[0m" if ansi else inner
    if func == "sequence":
        return render(node.get("children", []), ansi=ansi)
    # Fallback: try common child keys
    for key in ("body", "children", "child", "text"):
        if key in node:
            return render(node[key], ansi=ansi)
    return ""


def todo_record(item: object) -> dict[str, object]:
    """Normalize legacy content TODOs and structured TODO records."""
    if isinstance(item, dict) and "kind" in item and "body" in item:
        return {
            "kind": str(item.get("kind", "task")),
            "owner": str(item.get("owner", "author")),
            "audience": item.get("audience"),
            "source": item.get("source"),
            "status": str(item.get("status", "open")),
            "priority": str(item.get("priority", "normal")),
            "target": item.get("target"),
            "lean": item.get("lean"),
            "text": render(item.get("body")).strip() or "(empty)",
        }
    return {
        "kind": "task", "owner": "author", "audience": None,
        "source": None, "status": "open", "priority": "normal",
        "target": None, "lean": None,
        "text": render(item).strip() or "(empty)",
    }


def load_queue() -> dict[str, object]:
    """Load the non-rendered editorial decision queue."""
    try:
        data = json.loads(EDITORIAL_QUEUE.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"Could not load {EDITORIAL_QUEUE}: {exc}", file=sys.stderr)
        sys.exit(2)
    if not isinstance(data, dict) or not isinstance(data.get("items"), list):
        print(f"Invalid editorial queue schema in {EDITORIAL_QUEUE}", file=sys.stderr)
        sys.exit(2)
    return data


# --- Subcommands ---

def cmd_todo(args: argparse.Namespace) -> None:
    """List TODO items."""
    items = typst_query(args.entry, "<todo>")
    if args.n is not None:
        items = items[:args.n]

    if args.json_format == "typst":
        json.dump(items, sys.stdout, indent=2)
        print()
        return

    if args.json_format == "str":
        texts = [render(item).strip() or "(empty)" for item in items]
        json.dump(texts, sys.stdout, indent=2)
        print()
        return

    use_ansi = sys.stdout.isatty()
    records = [todo_record(item) for item in items]
    texts = [str(record["text"]) for record in records]

    if not texts:
        print("No TODOs found.")
        return
    width = len(str(len(texts)))
    for i, (record, text) in enumerate(zip(records, texts), 1):
        state = f"{record['status']}/{record['priority']}"
        print(f"  {i:>{width}}. [{record['kind']}/{record['owner']}; {state}] {text}")
    print(f"\n  {len(texts)} TODO(s)")


def cmd_status(args: argparse.Namespace) -> None:
    """Summarize editorial TODOs and notation migration markers."""
    todos = [todo_record(item) for item in typst_query(args.entry, "<todo>")]
    legacy = typst_query(args.entry, "<old-syntax>")
    migrations = typst_query(args.entry, "<notation-migration>")
    by_kind = Counter(str(item["kind"]) for item in todos)
    by_owner = Counter(str(item["owner"]) for item in todos)
    by_audience = Counter(str(item["audience"] or "unspecified") for item in todos)
    by_source = Counter(str(item["source"] or "unspecified") for item in todos)
    by_status = Counter(str(item["status"]) for item in todos)
    by_priority = Counter(str(item["priority"]) for item in todos)
    by_family = Counter(
        str(item.get("family", "unclassified"))
        if isinstance(item, dict) else "unclassified"
        for item in legacy
    )
    by_migration = Counter(
        f"{item.get('family', 'unclassified')}:{item.get('state', 'unknown')}"
        if isinstance(item, dict) else "unclassified:unknown"
        for item in migrations
    )
    report = {
        "todos": len(todos),
        "todos_by_kind": dict(sorted(by_kind.items())),
        "todos_by_owner": dict(sorted(by_owner.items())),
        "todos_by_audience": dict(sorted(by_audience.items())),
        "todos_by_source": dict(sorted(by_source.items())),
        "todos_by_status": dict(sorted(by_status.items())),
        "todos_by_priority": dict(sorted(by_priority.items())),
        "old_syntax": len(legacy),
        "old_syntax_by_family": dict(sorted(by_family.items())),
        "notation_migrations": dict(sorted(by_migration.items())),
    }
    if args.json_format:
        json.dump(report, sys.stdout, indent=2)
        print()
        return
    print(f"TODOs: {report['todos']}")
    for kind, count in report["todos_by_kind"].items():
        print(f"  {kind}: {count}")
    print("Owners:")
    for owner, count in report["todos_by_owner"].items():
        print(f"  {owner}: {count}")
    print("Audience:")
    for audience, count in report["todos_by_audience"].items():
        print(f"  {audience}: {count}")
    print("Source:")
    for source, count in report["todos_by_source"].items():
        print(f"  {source}: {count}")
    print("Status:")
    for status, count in report["todos_by_status"].items():
        print(f"  {status}: {count}")
    print("Priority:")
    for priority, count in report["todos_by_priority"].items():
        print(f"  {priority}: {count}")
    print(f"Old-syntax markers: {report['old_syntax']}")
    for family, count in report["old_syntax_by_family"].items():
        print(f"  {family}: {count}")
    print("Notation migration uses:")
    for family_state, count in report["notation_migrations"].items():
        print(f"  {family_state}: {count}")


LINT_PATTERNS = {
    "latex-layout-residue": re.compile(r"(?:minipage\s*=|scale\s*=)"),
    "zero-width-keyword-spacing": re.compile(
        r'(?:sans\((?:"(?:case|let|where)"|[cwl] [aeh] [set] [er])\))\s*#h\(0em\)'
        r'|#h\(0em\)\s*kw\("where"\)'
    ),
    "raw-angle-grammar": re.compile(r"\\?<[^>\n]+>\s*::="),
}


def cmd_lint(args: argparse.Namespace) -> None:
    """Find known conversion artifacts without changing source."""
    findings: list[tuple[str, Path, int, str]] = []
    for path in sorted((REPO_ROOT / "thesis").rglob("*.typ")):
        for line_no, line in enumerate(path.read_text().splitlines(), 1):
            for name, pattern in LINT_PATTERNS.items():
                if pattern.search(line):
                    findings.append((name, path.relative_to(REPO_ROOT), line_no, line.strip()))
    counts = Counter(name for name, _, _, _ in findings)
    for name, count in sorted(counts.items()):
        print(f"{name}: {count}")
    if args.details:
        for name, path, line_no, line in findings:
            print(f"{path}:{line_no}: {name}: {line}")
    if args.fail and findings:
        sys.exit(1)


def cmd_query(args: argparse.Namespace) -> None:
    """Run a raw typst query and print the JSON result."""
    items = typst_query(args.entry, args.selector, field=args.field)
    json.dump(items, sys.stdout, indent=2)
    print()


def queue_items(args: argparse.Namespace) -> list[dict[str, object]]:
    items = [item for item in load_queue()["items"] if isinstance(item, dict)]
    for field in ("status", "priority", "audience"):
        value = getattr(args, field, None)
        if value:
            items = [item for item in items if item.get(field) == value]
    return items


def queue_evidence_errors(items: list[dict[str, object]]) -> list[str]:
    """Check queue schema and cited source evidence."""
    lean_sources = list((REPO_ROOT / "formalization/thesis").rglob("*.lean"))
    lean_text = "\n".join(path.read_text() for path in lean_sources)
    errors: list[str] = []
    queue = load_queue()
    allowed_statuses = set(queue.get("statuses", []))
    allowed_priorities = set(queue.get("priorities", []))
    ids = [item.get("id") for item in items]
    for item_id, count in Counter(ids).items():
        if not isinstance(item_id, str) or not item_id:
            errors.append("queue item has no string id")
        elif count > 1:
            errors.append(f"duplicate queue id: {item_id}")
    for item in items:
        item_id = item.get("id", "(unknown)")
        for field in ("kind", "audience", "source", "target", "question"):
            if not isinstance(item.get(field), str) or not item.get(field):
                errors.append(f"{item_id}: missing string field {field}")
        if item.get("status") not in allowed_statuses:
            errors.append(f"{item_id}: unknown status {item.get('status')}")
        if item.get("priority") not in allowed_priorities:
            errors.append(f"{item_id}: unknown priority {item.get('priority')}")
        lean = item.get("lean")
        if not isinstance(lean, dict):
            continue
        evidence = lean.get("evidence", [])
        if not isinstance(evidence, list):
            errors.append(f"{item.get('id')}: lean.evidence is not a list")
            continue
        for ref in evidence:
            if not isinstance(ref, str):
                errors.append(f"{item.get('id')}: non-string evidence")
            elif "/" in ref or ref.endswith(".md") or ref.endswith(".lean"):
                if not (REPO_ROOT / ref).exists():
                    errors.append(f"{item.get('id')}: missing file {ref}")
            else:
                declaration = ref.rsplit(".", 1)[-1]
                pattern = rf"(?m)^(?:theorem|def|class|structure|inductive)\s+{re.escape(declaration)}\b"
                if not re.search(pattern, lean_text):
                    errors.append(f"{item.get('id')}: declaration not found: {ref}")
    return errors


def cmd_queue(args: argparse.Namespace) -> None:
    """Report the non-rendered ordering and formalization decision queue."""
    items = queue_items(args)
    if args.json_format:
        json.dump(items, sys.stdout, indent=2)
        print()
        return
    for item in items:
        print(
            f"{item.get('id')} [{item.get('priority')}/{item.get('status')}] "
            f"→ {item.get('audience')}: {item.get('question')}"
        )
        print(f"  target: {item.get('target')}")
        lean = item.get("lean")
        if isinstance(lean, dict):
            print(f"  Lean: {lean.get('status')}")
            for ref in lean.get("evidence", []):
                print(f"    evidence: {ref}")
            for missing in lean.get("missing", []):
                print(f"    missing: {missing}")
    print(f"\n{len(items)} queue item(s)")
    if args.check:
        errors = queue_evidence_errors(items)
        if errors:
            print("\nEvidence errors:", file=sys.stderr)
            for error in errors:
                print(f"  {error}", file=sys.stderr)
            sys.exit(1)
        print("Evidence references resolve.")


def source_paragraphs(path: Path) -> list[tuple[int, int, str, str]]:
    """Return editable source blocks with the nearest preceding heading."""
    lines = path.read_text().splitlines()
    heading = "(document start)"
    paragraphs: list[tuple[int, int, str, str]] = []
    start: int | None = None
    block: list[str] = []

    def flush(end: int) -> None:
        nonlocal start, block
        if start is not None:
            text = "\n".join(block).strip()
            if text and not text.startswith(("#import", "#show", "#let", "#set", "//", "/*")):
                paragraphs.append((start, end, heading, text))
        start, block = None, []

    for number, line in enumerate(lines, 1):
        match = re.match(r"^=+\s+(.+)$", line)
        if match:
            flush(number - 1)
            heading = match.group(1).strip()
            continue
        if not line.strip():
            flush(number - 1)
        else:
            if start is None:
                start = number
            block.append(line)
    flush(len(lines))
    return paragraphs


def cmd_review(args: argparse.Namespace) -> None:
    """Prompt the author to edit one existing source block; never draft prose."""
    path = (REPO_ROOT / args.file).resolve()
    try:
        path.relative_to(REPO_ROOT / "thesis")
    except ValueError:
        print("review --file must name a file under thesis/", file=sys.stderr)
        sys.exit(2)
    if not path.is_file() or path.suffix != ".typ":
        print(f"Typst source not found: {path}", file=sys.stderr)
        sys.exit(2)
    candidates = [p for p in source_paragraphs(path) if p[0] > args.after_line]
    if not candidates:
        print("No later source block found.")
        return
    start, end, heading, body = candidates[0]
    rel = path.relative_to(REPO_ROOT)
    print(f"REVIEW {rel}:{start}-{end} — {heading}")
    print("\nExisting source (edit it yourself; no replacement prose is generated):")
    print(body)
    print("\nDecide:")
    print("  1. Keep, delete, move, or fuse this block?")
    print("  2. What single job must it do in the chapter argument?")
    print("  3. Which notation/imported-paper assumptions must be migrated?")
    print("  4. Record unresolved choices in notes/editorial-queue.json or a structured #todo.")
    print(f"\nNext: python3 scripts/thesis.py review --file {rel} --after-line {end}")


def cmd_numbering(args: argparse.Namespace) -> None:
    """Audit configured full-document figure numbering in the Typst model."""
    figures = typst_query(args.entry, "figure", field=None)
    plain: list[tuple[int, str, str]] = []
    image_count = 0
    for index, figure in enumerate(figures, 1):
        if not isinstance(figure, dict) or figure.get("kind") != "image":
            continue
        image_count += 1
        numbering = str(figure.get("numbering", ""))
        # Subpanels are content inside one outer figure; theorem environments
        # have kind=thmenv and are intentionally excluded above.
        if re.fullmatch(r"[1aAiI]", numbering):
            caption = figure.get("caption")
            label = render(caption).strip() if caption else "(uncaptioned)"
            plain.append((index, numbering, label))
    print(f"Image figures queried: {image_count}")
    print(f"Plain global numbering configurations: {len(plain)}")
    if args.details:
        for index, numbering, caption in plain:
            print(f"  figure query item {index}: numbering={numbering!r}: {caption}")
    if args.fail and plain:
        sys.exit(1)


# --- CLI ---

def main() -> None:
    parser = argparse.ArgumentParser(
        prog="thesis",
        description="Thesis CLI utilities.",
    )
    parser.add_argument(
        "--entry", default=DEFAULT_ENTRY,
        help=f"Typst entry point (default: {DEFAULT_ENTRY})",
    )
    sub = parser.add_subparsers(dest="command")

    todo = sub.add_parser("todo", help="list TODO items")
    todo.add_argument(
        "-n", type=int, default=None, metavar="N",
        help="show only the first N TODOs",
    )
    todo.add_argument(
        "--json", nargs="?", const="str", choices=["str", "typst"],
        metavar="FORMAT", dest="json_format",
        help="output JSON (format: str [default], typst)",
    )

    query = sub.add_parser("query", help="run a raw typst query")
    query.add_argument(
        "selector", help="Typst selector (e.g. '<todo>', 'heading')",
    )

    status = sub.add_parser("status", help="summarize TODO and syntax migration status")
    status.add_argument("--json", action="store_true", dest="json_format")

    lint = sub.add_parser("lint", help="find known LaTeX-to-Typst conversion artifacts")
    lint.add_argument("--details", action="store_true", help="print each finding")
    lint.add_argument("--fail", action="store_true", help="exit nonzero when findings exist")
    query.add_argument(
        "--field", default="value",
        help="field to extract (default: value)",
    )

    queue = sub.add_parser(
        "queue", help="report non-rendered chapter and formalization decisions",
    )
    queue.add_argument("--status", help="filter by status")
    queue.add_argument("--priority", help="filter by priority")
    queue.add_argument("--audience", help="filter by audience")
    queue.add_argument("--json", action="store_true", dest="json_format")
    queue.add_argument(
        "--check", action="store_true",
        help="fail if cited evidence files or declarations cannot be found",
    )

    review = sub.add_parser(
        "review", help="prompt a paragraph-by-paragraph author editing pass",
    )
    review.add_argument("--file", required=True, help="Typst source under thesis/")
    review.add_argument(
        "--after-line", type=int, default=0,
        help="select the first source block starting after this line",
    )

    numbering = sub.add_parser(
        "numbering", help="audit full-thesis figure numbering configuration",
    )
    numbering.add_argument("--details", action="store_true")
    numbering.add_argument(
        "--fail", action="store_true",
        help="exit nonzero for image figures configured with plain global numbering",
    )

    args = parser.parse_args()
    if args.command is None:
        parser.print_help()
        sys.exit(1)
    if args.command == "todo":
        cmd_todo(args)
    elif args.command == "query":
        cmd_query(args)
    elif args.command == "status":
        cmd_status(args)
    elif args.command == "lint":
        cmd_lint(args)
    elif args.command == "queue":
        cmd_queue(args)
    elif args.command == "review":
        cmd_review(args)
    elif args.command == "numbering":
        cmd_numbering(args)


if __name__ == "__main__":
    main()
