#!/usr/bin/env python3
"""Audit and resolve imported cross-reference TODOs.

A reference is rewritten only when Typst reports one numbered target while
compiling the containing leaf by itself. Residual TODOs are classified against
the full thesis and source-label inventory.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
THESIS = ROOT / "thesis"

LABEL = re.compile(r"<([^>\n]+)>")
LABEL_NAME = re.compile(r"^[\w:.-]+$", re.UNICODE)
CROSSREF = re.compile(
    r"#todo\[Cross-reference: "
    r"(?:\\?@(?P<at>[^\].]+)(?P<at_dot>\.)?|`(?P<tick>[^`]+)`(?P<tick_dot>\.)?)"
    r"\]"
)
SOURCE_REF = re.compile(
    r"#todo\[Resolve source reference `(?P<label>[^`]+)` during integration\.\]"
)
CONDITIONAL_REF = re.compile(
    r'#conditional-ref\("(?P<label>[\w:.-]+)"\)'
)
SELECTORS = ("heading", "figure", "math.equation")


@dataclass(frozen=True)
class TodoRef:
    path: Path
    start: int
    end: int
    line: int
    label: str
    punctuation: str
    source_kind: str


@dataclass(frozen=True)
class Target:
    label: str
    selector: str
    numbered: bool


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    label: str
    classification: str
    source_kind: str


def normalize(raw: str) -> tuple[str, str]:
    """Separate punctuation accidentally imported as part of a label."""
    if raw.endswith("."):
        return raw[:-1], "."
    if raw.endswith(":"):
        return raw[:-1], ""
    return raw, ""


def labels_in_text(text: str) -> list[str]:
    return [label for label in LABEL.findall(text) if LABEL_NAME.fullmatch(label)]


def todo_refs(path: Path, text: str) -> list[TodoRef]:
    refs: list[TodoRef] = []
    for pattern, source_kind in ((CROSSREF, "cross-reference"), (SOURCE_REF, "source-reference")):
        for match in pattern.finditer(text):
            raw = (
                (match.groupdict().get("at") or match.groupdict().get("tick"))
                if source_kind == "cross-reference" else match.group("label")
            )
            label, embedded = normalize(raw)
            explicit = match.groupdict().get("at_dot") or match.groupdict().get("tick_dot") or ""
            refs.append(TodoRef(
                path=path,
                start=match.start(),
                end=match.end(),
                line=text.count("\n", 0, match.start()) + 1,
                label=label,
                punctuation=embedded or explicit,
                source_kind=source_kind,
            ))
    for match in CONDITIONAL_REF.finditer(text):
        refs.append(TodoRef(
            path=path,
            start=match.start(),
            end=match.end(),
            line=text.count("\n", 0, match.start()) + 1,
            label=match.group("label"),
            punctuation="",
            source_kind="conditional-reference",
        ))
    return sorted(refs, key=lambda ref: ref.start)


def query_targets(entry: Path) -> list[Target]:
    targets: list[Target] = []
    for selector in SELECTORS:
        result = subprocess.run(
            ["typst", "query", "--root", str(ROOT), str(entry.relative_to(ROOT)), selector],
            cwd=ROOT, text=True, capture_output=True, check=False,
        )
        if result.returncode != 0:
            raise RuntimeError(f"Typst query failed for {entry}:\n{result.stderr}")
        for record in json.loads(result.stdout):
            label = record.get("label")
            if not isinstance(label, str):
                continue
            label = label.removeprefix("<").removesuffix(">")
            targets.append(Target(
                label=label,
                selector=selector,
                numbered=record.get("numbering") is not None,
            ))
    return targets


def unique_numbered(targets: list[Target]) -> set[str]:
    counts = Counter(target.label for target in targets)
    return {
        target.label for target in targets
        if counts[target.label] == 1 and target.numbered
    }


def rewrite(
    text: str,
    refs: list[TodoRef],
    standalone_safe: set[str],
    assembled_safe: set[str],
) -> tuple[str, int]:
    parts: list[str] = []
    cursor = 0
    count = 0
    for ref in refs:
        parts.append(text[cursor:ref.start])
        if ref.source_kind == "conditional-reference":
            parts.append(text[ref.start:ref.end])
        elif ref.label in standalone_safe:
            parts.append(f"@{ref.label}{ref.punctuation}")
            count += 1
        elif ref.label in assembled_safe:
            parts.append(f'#conditional-ref("{ref.label}"){ref.punctuation}')
            count += 1
        else:
            parts.append(text[ref.start:ref.end])
        cursor = ref.end
    parts.append(text[cursor:])
    return "".join(parts), count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="rewrite standalone-safe references")
    parser.add_argument("--entry", default="thesis/main.typ")
    parser.add_argument("--json", action="store_true", dest="json_format")
    parser.add_argument(
        "--fail-resolvable", action="store_true",
        help="exit nonzero if a TODO can safely be rewritten",
    )
    args = parser.parse_args()

    texts = {path: path.read_text() for path in sorted(THESIS.rglob("*.typ"))}
    refs = [ref for path, text in texts.items() for ref in todo_refs(path, text)]
    label_paths: dict[str, list[Path]] = defaultdict(list)
    for path, text in texts.items():
        for label in labels_in_text(text):
            label_paths[label].append(path)

    full_targets = query_targets(ROOT / args.entry)
    full_counts = Counter(target.label for target in full_targets)
    full_numbered = unique_numbered(full_targets)

    # Query only leaves which have a same-source candidate. A full-document
    # target in another source is intentionally retained as cross-leaf-only.
    leaf_candidates = {
        ref.path for ref in refs
        if ref.label in full_numbered and label_paths.get(ref.label) == [ref.path]
    }
    leaf_safe: dict[Path, set[str]] = {}
    for path in sorted(leaf_candidates):
        leaf_safe[path] = unique_numbered(query_targets(path))

    findings: list[Finding] = []
    resolvable = 0
    changed: dict[Path, str] = {}
    for path, text in texts.items():
        path_refs = [ref for ref in refs if ref.path == path]
        safe = leaf_safe.get(path, set())
        assembled_safe = full_numbered - safe
        updated, count = rewrite(text, path_refs, safe, assembled_safe)
        resolvable += count
        if count:
            changed[path] = updated
        for ref in path_refs:
            source_count = len(label_paths.get(ref.label, []))
            if ref.source_kind == "conditional-reference" and ref.label in full_numbered:
                classification = "assembled-live-fallback"
            elif ref.label in safe:
                classification = "standalone-safe"
            elif source_count == 0:
                classification = "missing-target"
            elif source_count > 1 or full_counts[ref.label] > 1:
                classification = "duplicate"
            elif ref.label in full_numbered:
                classification = "assembled-safe"
            else:
                classification = "unnumbered"
            findings.append(Finding(
                path=str(path.relative_to(ROOT)), line=ref.line,
                label=ref.label, classification=classification,
                source_kind=ref.source_kind,
            ))

    if args.write:
        for path, updated in changed.items():
            path.write_text(updated)

    counts = Counter(finding.classification for finding in findings)
    report = {
        "total": len(findings),
        "source_lines": len({(finding.path, finding.line) for finding in findings}),
        "raw_todos": sum(
            finding.source_kind != "conditional-reference" for finding in findings
        ),
        "conditional_fallbacks": sum(
            finding.source_kind == "conditional-reference" for finding in findings
        ),
        "counts": dict(sorted(counts.items())),
        "findings": [asdict(finding) for finding in findings],
    }
    if args.json_format:
        json.dump(report, sys.stdout, indent=2)
        print()
    else:
        print(
            f"Tracked cross-reference sites: {len(findings)} occurrence(s) on "
            f"{report['source_lines']} source line(s)"
        )
        print(f"  raw TODOs: {report['raw_todos']}")
        print(f"  conditional fallbacks: {report['conditional_fallbacks']}")
        for classification, count in sorted(counts.items()):
            print(f"  {classification}: {count}")
        for finding in findings:
            print(
                f"{finding.path}:{finding.line}: {finding.classification}: "
                f"{finding.label}"
            )
    if args.fail_resolvable and resolvable:
        sys.exit(1)


if __name__ == "__main__":
    main()
