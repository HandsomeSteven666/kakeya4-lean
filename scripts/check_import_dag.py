#!/usr/bin/env python3
"""Check the module import graph: acyclic, and no `SecNN` imports another `SecNN`."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "Kakeya4"

IMPORT_RE = re.compile(r"^\s*import\s+(Kakeya4(?:\.[A-Za-z0-9_]+)*)", re.M)
SEC_RE = re.compile(r"^Sec\d+[a-z]?$")


def module_of(path: Path) -> str:
    rel = path.relative_to(ROOT).with_suffix("")
    parts = list(rel.parts)
    if parts[-1] == "default":
        parts = parts[:-1]
    return ".".join(parts)


def main() -> int:
    files = sorted(SRC.rglob("*.lean")) + [ROOT / "Kakeya4.lean"]
    graph: dict[str, list[str]] = {}
    for path in files:
        mod = module_of(path)
        text = path.read_text(encoding="utf-8")
        graph[mod] = [m for m in IMPORT_RE.findall(text) if m != mod]

    # `SecNN` must be a sink within the section layer.
    violations = []
    for mod, deps in graph.items():
        short = mod.rsplit(".", 1)[-1]
        if not SEC_RE.match(short):
            continue
        for d in deps:
            if SEC_RE.match(d.rsplit(".", 1)[-1]):
                violations.append(f"{mod} imports {d}")

    # Cycle detection (DFS).
    WHITE, GREY, BLACK = 0, 1, 2
    color = {m: WHITE for m in graph}
    cycles = []

    def dfs(u: str, stack: list[str]) -> None:
        color[u] = GREY
        stack.append(u)
        for v in graph.get(u, []):
            if v not in color:
                continue
            if color[v] == GREY:
                cycles.append(" -> ".join(stack[stack.index(v):] + [v]))
            elif color[v] == WHITE:
                dfs(v, stack)
        stack.pop()
        color[u] = BLACK

    for m in graph:
        if color[m] == WHITE:
            dfs(m, [])

    if violations:
        print("section-layer violations:", file=sys.stderr)
        for v in violations:
            print("  " + v, file=sys.stderr)
    if cycles:
        print("import cycles:", file=sys.stderr)
        for c in cycles:
            print("  " + c, file=sys.stderr)
    if violations or cycles:
        return 1
    print(f"import graph ok: {len(graph)} modules, no cycles, Sec* are sinks")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
