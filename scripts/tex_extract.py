#!/usr/bin/env python3
"""Extract theorem-like environments from the manuscript LaTeX sources.

The parser is a stack-based environment scanner (not a regex over `\\end{...}`),
because statement bodies routinely contain nested `equation`, `align`, `itemize`
and `figure` environments.

Outputs (deterministic, LF, UTF-8 without BOM):
  ir/statements.json   one record per theorem/lemma/proposition/definition/corollary
  ir/deps.json         edges among the extracted labels
  ir/coverage.md       per-section counts (must total 81)

Usage:
  python scripts/tex_extract.py
  python scripts/tex_extract.py --check   # exit 1 if outputs are stale
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SEC_DIR = ROOT / "vendor" / "openai-math" / "sections"
IR_DIR = ROOT / "ir"

TARGET_ENVS = ("theorem", "lemma", "proposition", "definition", "corollary")
EXTRA_ENVS = ("remark", "example", "conjecture")

BEGIN_RE = re.compile(r"\\begin\{([A-Za-z*]+)\}")
END_RE = re.compile(r"\\end\{([A-Za-z*]+)\}")
LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
REF_RE = re.compile(r"\\(?:Cref|cref|ref|eqref)\{([^}]+)\}")
SECTION_RE = re.compile(r"^(\d+)([a-z]?)-")


def strip_comments(text: str) -> str:
    """Blank out `%` comments while preserving character offsets and newlines."""
    out = []
    for line in text.splitlines(keepends=True):
        i = 0
        cut = None
        while i < len(line):
            if line[i] == "\\":
                i += 2
                continue
            if line[i] == "%":
                cut = i
                break
            i += 1
        if cut is None:
            out.append(line)
        else:
            out.append(line[:cut] + "\n")
    return "".join(out)


def line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def parse_file(path: Path) -> tuple[list[dict], dict[str, dict]]:
    raw = path.read_text(encoding="utf-8")
    text = strip_comments(raw)
    m = SECTION_RE.match(path.name)
    if not m:
        raise ValueError(f"cannot infer section from {path.name}")
    section = m.group(1) + m.group(2)

    records: list[dict] = []
    stack: list[tuple[str, int]] = []  # (environment, start offset of \begin)
    index = 0

    for match in re.finditer(r"\\(begin|end)\{([A-Za-z*]+)\}", text):
        kind, env = match.group(1), match.group(2)
        if kind == "begin":
            stack.append((env, match.start()))
            continue
        # kind == "end": pop the matching environment
        if not stack or stack[-1][0] != env:
            # unbalanced source; ignore rather than crash
            continue
        _, start = stack.pop()
        if env not in TARGET_ENVS and env not in EXTRA_ENVS:
            continue
        if stack:
            # only top-level statement environments (nested theorems do not occur)
            continue
        body_start = text.find("}", start) + 1
        body = text[body_start:match.start()]
        label_m = LABEL_RE.search(body)
        label = label_m.group(1) if label_m else None
        # Remove the statement's own label line entirely (leaving a blank line inside a
        # display-math environment would break TeX), then drop any remaining inline labels
        # belonging to equations nested in the statement.
        body_clean = re.sub(r"(?m)^[ \t]*\\label\{[^}]*\}[ \t]*\r?\n", "", body)
        body_clean = LABEL_RE.sub("", body_clean).strip()
        index += 1
        if label is None:
            label = f"sec{section}:{env}-{index}"
        title = None
        t = body.lstrip()
        if t.startswith("["):
            depth, j = 0, 0
            for j, ch in enumerate(t):
                if ch == "[":
                    depth += 1
                elif ch == "]":
                    depth -= 1
                    if depth == 0:
                        break
            title = t[1:j].strip()
        records.append(
            {
                "label": label,
                "env": env,
                "section": section,
                "tex_file": f"sections/{path.name}",
                "line_start": line_of(text, start),
                "line_end": line_of(text, match.end()),
                "title": title,
                "statement_tex": body_clean,
                "refs": [],
            }
        )

    return records, {}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()

    files = sorted(SEC_DIR.glob("*.tex"))
    if not files:
        print(f"no .tex files under {SEC_DIR}", file=sys.stderr)
        return 2

    all_records: list[dict] = []
    for path in files:
        recs, _ = parse_file(path)
        all_records.extend(recs)

    all_records.sort(key=lambda r: (r["section"], r["line_start"]))
    known = {r["label"] for r in all_records}
    for r in all_records:
        r["refs"] = sorted({x for x in REF_RE.findall(r["statement_tex"]) if x in known})

    edges = [{"from": r["label"], "to": t} for r in all_records for t in r["refs"]]

    counts: dict[str, int] = {}
    for r in all_records:
        if r["env"] in TARGET_ENVS:
            counts[r["section"]] = counts.get(r["section"], 0) + 1

    statements = [r for r in all_records if r["env"] in TARGET_ENVS]
    extras = [r for r in all_records if r["env"] not in TARGET_ENVS]

    IR_DIR.mkdir(exist_ok=True)
    payload = {
        "source": "openai/math",
        "commit": json.loads((ROOT / "vendor" / "openai-math" / "PROVENANCE.json").read_text(encoding="utf-8"))["commit"],
        "total": len(statements),
        "statements": statements,
        "extras": extras,
    }
    deps = {"nodes": [r["label"] for r in statements], "edges": edges}

    lines = ["# Coverage of manuscript environments", "",
             f"Raw theorem-like environments: **{len(statements) + len(extras)}** "
             f"(of which {len(extras)} is a remark, not formalized).",
             f"Formalizable statement environments (theorem/lemma/proposition/definition/corollary): "
             f"**{len(statements)}**.", "",
             "| Section | Count |", "| --- | --- |"]
    for sec in sorted(counts, key=lambda s: (int(re.match(r"\d+", s).group()), s)):
        lines.append(f"| {sec} | {counts[sec]} |")
    lines.append(f"| **total** | **{len(statements)}** |")
    lines.append("")
    lines.append(f"Additional remark/example/conjecture environments (not formalized): {len(extras)}")
    coverage = "\n".join(lines) + "\n"

    outputs = {
        IR_DIR / "statements.json": json.dumps(payload, ensure_ascii=False, indent=1) + "\n",
        IR_DIR / "deps.json": json.dumps(deps, ensure_ascii=False, indent=1) + "\n",
        IR_DIR / "coverage.md": coverage,
    }

    if args.check:
        bad = []
        for path, content in outputs.items():
            if not path.exists() or path.read_text(encoding="utf-8") != content:
                bad.append(str(path.relative_to(ROOT)))
        if bad:
            print("stale: " + ", ".join(bad), file=sys.stderr)
            return 1
        print("up to date")
        return 0

    for path, content in outputs.items():
        path.write_text(content, encoding="utf-8", newline="\n")
    print(f"extracted {len(statements)} statements ({len(extras)} extras) -> {IR_DIR}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
