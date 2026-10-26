#!/usr/bin/env python3
"""Verify that every Lean docstring reproduces the manuscript statement verbatim."""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PAYLOAD = json.loads((ROOT / "ir" / "statements.json").read_text(encoding="utf-8"))


def lean_name(label: str) -> str:
    s = re.sub(r"[^A-Za-z0-9_]", "_", label)
    s = re.sub(r"_+", "_", s).strip("_")
    if not s or s[0].isdigit():
        s = "s_" + s
    return s + "_statement"


def main() -> int:
    bad = []
    for r in PAYLOAD["statements"]:
        sec = r["section"].replace(".", "_")
        path = ROOT / "Kakeya4" / f"Sec{sec}.lean"
        text = path.read_text(encoding="utf-8") if path.exists() else ""
        expected = r["statement_tex"].replace("-/", "- /")
        if expected not in text:
            bad.append(f"Sec{sec}.lean / {r['label']}")
    if bad:
        print("docstring text does not match the manuscript:", file=sys.stderr)
        for x in bad:
            print("  " + x, file=sys.stderr)
        return 1
    print(f"docstrings verified: {len(PAYLOAD['statements'])}/{len(PAYLOAD['statements'])}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
