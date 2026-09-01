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


# --- Typst helpers ---

def typst_query(entry: str, selector: str, *, field: str = "value") -> list[object]:
    """Run `typst query` and return the parsed JSON list."""
    result = subprocess.run(
        ["typst", "query", "--root", str(REPO_ROOT), entry, selector, "--field", field],
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


def todo_record(item: object) -> tuple[str, str, str]:
    """Normalize legacy content TODOs and structured TODO records."""
    if isinstance(item, dict) and "kind" in item and "body" in item:
        return (
            str(item.get("kind", "task")),
            str(item.get("owner", "author")),
            render(item.get("body")).strip() or "(empty)",
        )
    return ("task", "author", render(item).strip() or "(empty)")


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
    texts = [text for _, _, text in records]

    if not texts:
        print("No TODOs found.")
        return
    width = len(str(len(texts)))
    for i, ((kind, owner, _), text) in enumerate(zip(records, texts), 1):
        print(f"  {i:>{width}}. [{kind}/{owner}] {text}")
    print(f"\n  {len(texts)} TODO(s)")


def cmd_status(args: argparse.Namespace) -> None:
    """Summarize editorial TODOs and notation migration markers."""
    todos = [todo_record(item) for item in typst_query(args.entry, "<todo>")]
    legacy = typst_query(args.entry, "<old-syntax>")
    migrations = typst_query(args.entry, "<notation-migration>")
    by_kind = Counter(kind for kind, _, _ in todos)
    by_owner = Counter(owner for _, owner, _ in todos)
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


if __name__ == "__main__":
    main()
