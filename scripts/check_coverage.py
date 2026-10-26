#!/usr/bin/env python3
"""Check that every extracted manuscript statement has a Lean placeholder and a blueprint node."""

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
    missing_lean = []
    missing_bp = []
    for r in PAYLOAD["statements"]:
        sec = r["section"].replace(".", "_")
        name = lean_name(r["label"])
        lean_file = ROOT / "Kakeya4" / f"Sec{sec}.lean"
        bp_file = ROOT / "blueprint" / "src" / "chapters" / f"sec{sec}.tex"

        lean_text = lean_file.read_text(encoding="utf-8") if lean_file.exists() else ""
        if not re.search(rf"\bdef\s+{re.escape(name)}\s*:", lean_text):
            missing_lean.append(f"{lean_file.name}:{r['label']}")

        bp_text = bp_file.read_text(encoding="utf-8") if bp_file.exists() else ""
        if (
            f"\\label{{{r['label']}}}" not in bp_text
            or f"\\lean{{Kakeya4.Sec{sec}.{name}}}" not in bp_text
        ):
            missing_bp.append(f"{bp_file.name}:{r['label']}")

    total = len(PAYLOAD["statements"])
    print(f"statements: {total}")
    if missing_lean:
        print("missing Lean placeholders:", file=sys.stderr)
        for x in missing_lean:
            print("  " + x, file=sys.stderr)
    if missing_bp:
        print("missing blueprint nodes:", file=sys.stderr)
        for x in missing_bp:
            print("  " + x, file=sys.stderr)
    if missing_lean or missing_bp:
        return 1
    print(f"coverage ok: {total}/{total}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
