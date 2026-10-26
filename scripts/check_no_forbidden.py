#!/usr/bin/env python3
"""Reject constructs that would hide or bypass a proof obligation.

Forbidden everywhere:
  * `axiom` declarations
  * `native_decide`
  * `unsafe` definitions
  * `implemented_by`

Forbidden in `Kakeya4/Hard/Externals/`:
  * `:= True` / `:= False` (a vacuous external input)

`sorry` is *not* rejected: it is the tracked development currency. See check_sorry.py.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "Kakeya4"

RULES = [
    (re.compile(r"^\s*(?:private\s+|protected\s+)?axiom\b", re.M), "axiom declaration"),
    (re.compile(r"\bnative_decide\b"), "native_decide"),
    (re.compile(r"\bunsafe\s+(?:def|theorem|lemma|instance)\b"), "unsafe declaration"),
    (re.compile(r"\bimplemented_by\b"), "implemented_by"),
]


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def main() -> int:
    bad = []
    for path in sorted(SRC.rglob("*.lean")):
        code = strip_comments(path.read_text(encoding="utf-8"))
        for pattern, what in RULES:
            for m in pattern.finditer(code):
                line = code.count("\n", 0, m.start()) + 1
                bad.append((str(path.relative_to(ROOT)), line, what))
        for m in re.finditer(r":=\s*(True|False)\b", code):
            line = code.count("\n", 0, m.start()) + 1
            bad.append((str(path.relative_to(ROOT)), line, "vacuous proposition body"))
        for m in re.finditer(r":=\s*by\s+trivial\b", code):
            line = code.count("\n", 0, m.start()) + 1
            bad.append((str(path.relative_to(ROOT)), line, "vacuous `by trivial` body"))

    if bad:
        for path, line, what in bad:
            print(f"{path}:{line}: forbidden: {what}", file=sys.stderr)
        return 1
    print(f"no forbidden constructs in {len(list(SRC.rglob('*.lean')))} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
