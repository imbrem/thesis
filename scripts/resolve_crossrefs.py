#!/usr/bin/env python3
"""Resolve imported cross-reference TODOs when an exact Typst label exists."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
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


def labels_in_text(text: str) -> set[str]:
    return {
        label for label in LABEL.findall(text)
        if LABEL_NAME.fullmatch(label)
    }


def source_labels() -> set[str]:
    labels: set[str] = set()
    for path in THESIS.rglob("*.typ"):
        labels.update(labels_in_text(path.read_text()))
    return labels


def todo_targets() -> set[str]:
    targets: set[str] = set()
    for path in THESIS.rglob("*.typ"):
        text = path.read_text()
        for match in CROSSREF.finditer(text):
            raw = match.group("at") or match.group("tick")
            targets.add(normalize(raw)[0])
        for match in SOURCE_REF.finditer(text):
            targets.add(normalize(match.group("label"))[0])
    return targets


def referenceable_labels(labels: set[str], entry: str) -> set[str]:
    """Ask Typst which exact labels uniquely target referenceable elements."""
    occurrences: dict[str, int] = {}
    for selector in ("heading", "figure", "math.equation"):
        result = subprocess.run(
            [
                "typst", "query", "--root", str(ROOT), entry, selector,
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        if result.returncode != 0:
            raise RuntimeError(result.stderr)
        for record in json.loads(result.stdout):
            label = record.get("label")
            if not isinstance(label, str):
                continue
            label = label.removeprefix("<").removesuffix(">")
            if label not in labels:
                continue
            if selector == "math.equation" and record.get("numbering") is None:
                continue
            occurrences[label] = occurrences.get(label, 0) + 1
    return {label for label, count in occurrences.items() if count == 1}


def normalize(raw: str) -> tuple[str, str]:
    """Return a likely label and punctuation accidentally imported with it."""
    if raw.endswith((".", ":")):
        return raw[:-1], "." if raw.endswith(".") else ""
    return raw, ""


def resolve(text: str, labels: set[str]) -> tuple[str, int]:
    count = 0

    def crossref(match: re.Match[str]) -> str:
        nonlocal count
        raw = match.group("at") or match.group("tick")
        label, embedded = normalize(raw)
        if label not in labels:
            return match.group(0)
        count += 1
        explicit_dot = match.group("at_dot") or match.group("tick_dot") or ""
        return f"@{label}{embedded or explicit_dot}"

    def source_ref(match: re.Match[str]) -> str:
        nonlocal count
        label, _ = normalize(match.group("label"))
        if label not in labels:
            return match.group(0)
        count += 1
        return f"@{label}"

    text = CROSSREF.sub(crossref, text)
    text = SOURCE_REF.sub(source_ref, text)
    return text, count


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="rewrite matching files")
    parser.add_argument("--entry", default="thesis/main.typ")
    args = parser.parse_args()

    candidates = source_labels() & todo_targets()
    labels = referenceable_labels(candidates, args.entry)
    total = 0
    changed: list[tuple[Path, str]] = []
    for path in sorted(THESIS.rglob("*.typ")):
        original = path.read_text()
        # CI compiles every imported leaf independently, so an apparently
        # valid full-document reference is safe only when its target is also
        # present in that leaf.
        updated, count = resolve(original, labels & labels_in_text(original))
        if count:
            total += count
            changed.append((path, updated))

    print(f"Resolvable exact cross-reference TODOs: {total}")
    for path, _ in changed:
        print(path.relative_to(ROOT))
    if args.write:
        for path, updated in changed:
            path.write_text(updated)


if __name__ == "__main__":
    main()
