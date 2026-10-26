#!/usr/bin/env python3
"""Check the external-input dependency registry.

The registry `ir/dependencies.json` is the single source of truth for the status of the five
published inputs used by the main theorem:

  opaque  -- `def ... : Prop := by sorry` (statement not formalized; `sorryAx` in the audit)
  stated  -- a real `Prop`, no `sorry`, but not proved
  proved  -- a complete theorem

Checks:
  1. schema and uniqueness;
  2. the fields of `structure ExternalInputs` match the registry exactly;
  3. static status check (opaque bodies are `by sorry`; stated bodies are sorry-free);
  4. overlay cross-check (the curated label set is exactly the stated set);
  5. a Lean probe: `#print axioms` must show `sorryAx` for opaque entries and must not show
     it for stated entries; the wiring theorem must be clean.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEPS = ROOT / "ir" / "dependencies.json"
BUNDLE = ROOT / "Kakeya4" / "Hard" / "Externals" / "Bundle.lean"
OVERLAY = ROOT / "scripts" / "overlay" / "statements.curated.json"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
STATUSES = {"opaque", "stated", "proved"}


def short(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def normalized_hash(path: Path) -> str:
    import hashlib

    text = path.read_text(encoding="utf-8")
    return hashlib.sha256(re.sub(r"\s+", " ", text).strip().encode()).hexdigest()


def bundle_fields() -> dict[str, str]:
    """Return {field: type} for `structure ExternalInputs`."""
    text = BUNDLE.read_text(encoding="utf-8")
    block = re.search(r"structure\s+ExternalInputs\b.*?:=\s*(.*?)\n\n", text, re.S)
    if not block:
        block = re.search(r"structure\s+ExternalInputs\b(.*?)\n\n", text, re.S)
    if not block:
        raise SystemExit("cannot locate structure ExternalInputs in Bundle.lean")
    fields: dict[str, str] = {}
    in_comment = False
    for line in block.group(1).splitlines():
        stripped = line.strip()
        if stripped.startswith("/--"):
            in_comment = not stripped.endswith("-/")
            continue
        if in_comment:
            in_comment = not stripped.endswith("-/")
            continue
        if not stripped or stripped.startswith("--"):
            continue
        m = re.match(r"(\w+)\s*:\s*([A-Za-z0-9_.]+)", stripped)
        if m:
            fields[m.group(1)] = m.group(2)
    return fields


def lean_probe(names: list[str], imports: list[str]) -> dict[str, set[str] | None]:
    script = "".join(f"import {m}\n" for m in sorted(set(imports)))
    script += "\n".join(f"#print axioms {n}" for n in names) + "\n"
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "1")
    proc = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT, input=script, capture_output=True, text=True, env=env,
    )
    if proc.returncode != 0:
        print(proc.stdout + proc.stderr, file=sys.stderr)
        raise SystemExit("Lean probe failed")
    out = proc.stdout + proc.stderr
    result: dict[str, set[str] | None] = {}
    for line in out.splitlines():
        m = re.match(r"'([^']+)' depends on axioms: \[([^\]]*)\]", line)
        if m:
            result[m.group(1)] = {x.strip() for x in m.group(2).split(",") if x.strip()}
            continue
        m = re.match(r"'([^']+)' does not depend on any axioms", line)
        if m:
            result[m.group(1)] = set()
    return result


def main() -> int:
    data = json.loads(DEPS.read_text(encoding="utf-8"))
    deps = data.get("dependencies", [])
    problems: list[str] = []

    # 1. schema
    if data.get("version") != 1:
        problems.append("version must be 1")
    if len(deps) != 5:
        problems.append(f"expected 5 dependencies, got {len(deps)}")
    ids = [d.get("id") for d in deps]
    if len(ids) != len(set(ids)):
        problems.append("duplicate dependency id")
    for d in deps:
        for key in ("id", "status", "lean_name", "lean_module", "bundle_field"):
            if not d.get(key):
                problems.append(f"{d.get('id', '?')}: missing {key}")
        if d.get("status") not in STATUSES:
            problems.append(f"{d.get('id', '?')}: bad status {d.get('status')!r}")

    # 2. bundle fields
    fields = bundle_fields()
    registry_fields = {d["bundle_field"]: d for d in deps if "bundle_field" in d}
    if set(fields) != set(registry_fields):
        problems.append(
            f"bundle fields {sorted(fields)} != registry {sorted(registry_fields)}"
        )
    for name, typ in fields.items():
        d = registry_fields.get(name)
        if not d:
            continue
        expected = short(d.get("alias_name") or d["lean_name"])
        if short(typ) != expected:
            problems.append(f"bundle field {name}: type {typ} != {expected}")

    # 3. static status
    for d in deps:
        path = module_path(d["lean_module"])
        if not path.exists():
            problems.append(f"{d['id']}: missing module {path}")
            continue
        text = path.read_text(encoding="utf-8")
        name = short(d["lean_name"])
        m = re.search(
            rf"(?m)^(?:noncomputable\s+)?(?:def|abbrev)\s+{re.escape(name)}\s*:\s*Prop\s*:=\s*",
            text,
        )
        if not m:
            problems.append(f"{d['id']}: cannot find `def {name} : Prop` in {d['lean_module']}")
            continue
        tail = text[m.end():m.end() + 120]
        if d["status"] == "opaque":
            if not re.match(r"by\s+sorry\b", tail):
                problems.append(f"{d['id']}: opaque body is not `by sorry`: {tail[:60]!r}")
        else:
            if re.match(r"by\s+sorry\b", tail) or "sorry" in tail.split("\n\n")[0]:
                problems.append(f"{d['id']}: stated body contains sorry")
            if re.search(r":=\s*(True|False)\b", tail) or "by trivial" in tail:
                problems.append(f"{d['id']}: stated body is vacuous: {tail[:60]!r}")
        if d["status"] == "stated":
            expected = d.get("source_sha256")
            actual = normalized_hash(path)
            if expected != actual:
                problems.append(
                    f"{d['id']}: source hash mismatch ({expected} != {actual}); "
                    "update ir/dependencies.json after review"
                )

    # 4. overlay cross-check
    overlay = json.loads(OVERLAY.read_text(encoding="utf-8")).get("entries", {}) if OVERLAY.exists() else {}
    stated = {d.get("overlay_label") for d in deps if d["status"] == "stated"}
    if not stated <= set(overlay):
        problems.append(
            f"stated external inputs missing from overlay: {sorted(stated - set(overlay))}"
        )
    for d in deps:
        if d["status"] == "stated" and d.get("overlay_label") in overlay:
            expr = overlay[d["overlay_label"]].get("lean_expr")
            if expr != d["lean_name"]:
                problems.append(f"{d['id']}: overlay lean_expr {expr} != {d['lean_name']}")

    # 5. Lean probe
    probe_names = [d["lean_name"] for d in deps]
    imports = sorted({d["lean_module"] for d in deps})
    for d in deps:
        if d["status"] == "stated":
            for key in ("alias_name", "statement_alias", "wiring_theorem"):
                if d.get(key):
                    probe_names.append(d[key])
            imports.append("Kakeya4.Sec02")
    axioms = lean_probe(probe_names, imports)

    for d in deps:
        name = d["lean_name"]
        if name not in axioms:
            problems.append(f"{d['id']}: no axiom line for {name}")
            continue
        ax = axioms[name]
        if d["status"] == "opaque":
            if "sorryAx" not in ax:
                problems.append(f"{d['id']}: opaque entry has no sorryAx")
        else:
            if "sorryAx" in ax:
                problems.append(f"{d['id']}: stated entry has sorryAx")
            extra = ax - STANDARD
            if extra:
                problems.append(f"{d['id']}: non-standard axioms {sorted(extra)}")
        if d["status"] == "stated":
            for key in ("alias_name", "statement_alias", "wiring_theorem"):
                n = d.get(key)
                if n and n in axioms and "sorryAx" in axioms[n]:
                    problems.append(f"{d['id']}: {key} {n} has sorryAx")

    if problems:
        for p in problems:
            print("FAIL: " + p, file=sys.stderr)
        return 1

    counts = {s: sum(1 for d in deps if d["status"] == s) for s in STATUSES}
    print(
        "dependency registry ok: "
        + ", ".join(f"{counts[s]} {s}" for s in ("proved", "stated", "opaque"))
    )
    for d in deps:
        print(f"  {d['status']:6s}  {d['id']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
