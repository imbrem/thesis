#!/usr/bin/env python3
# pyright: basic
"""Thesis status queries via Typst.

Subcommands query Typst metadata (TODOs, chapters, etc.) and render
results to the terminal or as JSON.
"""

from __future__ import annotations

import argparse
import json
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
    texts = [render(item, ansi=use_ansi).strip() or "(empty)" for item in items]

    if not texts:
        print("No TODOs found.")
        return
    width = len(str(len(texts)))
    for i, text in enumerate(texts, 1):
        print(f"  {i:>{width}}. {text}")
    print(f"\n  {len(texts)} TODO(s)")


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


if __name__ == "__main__":
    main()
