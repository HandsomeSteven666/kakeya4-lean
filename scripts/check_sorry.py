#!/usr/bin/env python3
"""Count `sorry` occurrences and enforce a monotone baseline.

Statement-level gaps are the `def ..._statement : Prop := by sorry` placeholders generated
from the manuscript; proof-level gaps are `sorry`s inside actual proofs. Both are counted,
but reported separately.

Writes docs/SORRY.md and compares the total with docs/sorry-baseline.json (only decreases
are accepted).
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "Kakeya4"
BASELINE = ROOT / "docs" / "sorry-baseline.json"
REPORT = ROOT / "docs" / "SORRY.md"


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--write", action="store_true", help="write docs/SORRY.md and baseline")
    args = ap.parse_args()

    rows = []
    stmt_total = proof_total = 0
    for path in sorted(SRC.rglob("*.lean")):
        code = strip_comments(path.read_text(encoding="utf-8"))
        hits = len(re.findall(r"\bsorry\b", code))
        if not hits:
            continue
        # A placeholder is a `def <name> : Prop := by sorry` (statement not yet formalized).
        placeholders = len(
            re.findall(r"\bdef\s+\w+\s*:\s*Prop\s*:=\s*by\s*sorry", code)
        )
        stmt_total += placeholders
        proof_total += hits - placeholders
        rows.append((str(path.relative_to(ROOT)), hits, placeholders, hits - placeholders))

    total = stmt_total + proof_total
    lines = [
        "# Sorry inventory",
        "",
        "| File | total | statement-level | proof-level |",
        "| --- | ---: | ---: | ---: |",
    ]
    for name, hits, stmt, proof in rows:
        lines.append(f"| `{name}` | {hits} | {stmt} | {proof} |")
    lines += [
        f"| **total** | **{total}** | **{stmt_total}** | **{proof_total}** |",
        "",
        "Statement-level gaps are `def …_statement : Prop := by sorry` placeholders: the",
        "manuscript's objects are not formalized yet, so the proposition itself is a `sorry`.",
        "Proof-level gaps are `sorry`s inside theorems whose statements are real.",
        "",
    ]
    report = "\n".join(lines) + "\n"

    if args.write:
        REPORT.write_text(report, encoding="utf-8", newline="\n")
        BASELINE.write_text(
            json.dumps({"total": total, "statement": stmt_total, "proof": proof_total}, indent=1) + "\n",
            encoding="utf-8",
            newline="\n",
        )
        print(f"wrote {REPORT.relative_to(ROOT)} and baseline ({total})")
        return 0

    if not BASELINE.exists():
        print(report)
        print(f"no baseline at {BASELINE.relative_to(ROOT)}; run with --write", file=sys.stderr)
        return 2

    base = json.loads(BASELINE.read_text(encoding="utf-8"))
    print(report)
    if total > base["total"]:
        print(f"sorry count increased: {base['total']} -> {total}", file=sys.stderr)
        return 1
    print(f"sorry count ok: {total} <= baseline {base['total']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
