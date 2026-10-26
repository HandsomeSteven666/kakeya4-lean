#!/usr/bin/env python3
"""Validate the zone registry ir/zones.json against the manuscript IR and Lean tree.

Checks:
  1. schema: version, legend, counts;
  2. the 80 statement labels match ir/statements.json exactly (bijection);
  3. zone/owner/status enums are valid; Lean names are well-formed;
  4. deps / blockers refer to known statement labels, hard work item ids, or external input ids;
  5. hard work items have dossiers under docs/hard/ and valid external input references;
  6. modules: every current Lean file under Kakeya4/ (plus the root Kakeya4.lean) is registered,
     paths exist, targets are under Foundation/Construction/Hard/;
  7. the 5 registered external inputs map to the expected zone entries;
  8. prints per-zone counts.

Exit code 0 iff no problems. Read-only: never writes files.
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ZONES = ROOT / "ir" / "zones.json"
STATEMENTS = ROOT / "ir" / "statements.json"
DEPS = ROOT / "ir" / "dependencies.json"
LEAN_DIR = ROOT / "Kakeya4"
HARD_DOCS = ROOT / "docs" / "hard"

ZONE_ENUM = {"foundation", "construction", "hard", "index", "audit", "root"}
OWNER_ENUM = {"ai", "human", "ai+human"}
STATUS_ENUM = {"proved", "stated", "unformalized", "pending", "active", "done", "escalated", "blocked",
               "opaque", "unmodeled"}
TARGET_PREFIX = {"foundation": "Kakeya4/Foundation/", "construction": "Kakeya4/Construction/",
                 "hard": "Kakeya4/Hard/"}
LEAN_RE = re.compile(r"^Kakeya4\.Sec[0-9a-z_]+\.\w+$")


def main() -> int:
    problems: list[str] = []

    zones = json.loads(ZONES.read_text(encoding="utf-8"))
    statements = json.loads(STATEMENTS.read_text(encoding="utf-8"))["statements"]
    deps = json.loads(DEPS.read_text(encoding="utf-8"))["dependencies"]

    if zones.get("version") != 1:
        problems.append("zones.json: version must be 1")

    # 2. label bijection
    expected = [s["label"] for s in statements]
    actual = [s.get("id") for s in zones.get("statements", [])]
    if sorted(expected) != sorted(actual):
        problems.append(f"labels mismatch: missing={sorted(set(expected) - set(actual))} "
                        f"extra={sorted(set(actual) - set(expected))}")
    if len(actual) != len(set(actual)):
        problems.append("duplicate statement ids in zones.json")

    item_ids = [it.get("id") for it in zones.get("hard_workitems", [])]
    ext_ids = [x.get("id") for x in zones.get("external_inputs", [])]
    if len(item_ids) != len(set(item_ids)):
        problems.append("duplicate hard_workitems ids")
    if len(ext_ids) != len(set(ext_ids)):
        problems.append("duplicate external_inputs ids")
    known_refs = set(expected) | set(item_ids) | set(ext_ids)
    zone_of = {s["id"]: s["zone"] for s in zones.get("statements", [])}

    for s in zones.get("statements", []):
        sid = s.get("id", "?")
        if s.get("zone") not in ZONE_ENUM:
            problems.append(f"{sid}: bad zone {s.get('zone')!r}")
        if s.get("owner") not in OWNER_ENUM:
            problems.append(f"{sid}: bad owner {s.get('owner')!r}")
        if s.get("status") not in STATUS_ENUM:
            problems.append(f"{sid}: bad status {s.get('status')!r}")
        if not LEAN_RE.match(str(s.get("lean", ""))):
            problems.append(f"{sid}: bad lean name {s.get('lean')!r}")
        for dep in s.get("deps", []):
            if dep not in known_refs:
                problems.append(f"{sid}: unknown dep {dep!r}")

    # 4-5. hard work items
    for it in zones.get("hard_workitems", []):
        iid = it.get("id", "?")
        if it.get("zone", "hard") != "hard":
            problems.append(f"{iid}: hard_workitem must have zone=hard")
        if it.get("owner") not in OWNER_ENUM:
            problems.append(f"{iid}: bad owner")
        if it.get("status") not in STATUS_ENUM:
            problems.append(f"{iid}: bad status {it.get('status')!r}")
        if not sorted(HARD_DOCS.glob(f"{iid}-*.md")):
            problems.append(f"{iid}: missing docs/hard/{iid}-*.md dossier")
        for b in it.get("blocks", []):
            if b not in known_refs:
                problems.append(f"{iid}: unknown blocker {b!r}")
        for x in it.get("external_inputs", []):
            if x not in known_refs:
                problems.append(f"{iid}: unknown external input {x!r}")

    # construction work items (same schema as hard, no dossier requirement)
    cw_ids = [it.get("id") for it in zones.get("construction_workitems", [])]
    if len(cw_ids) != len(set(cw_ids)):
        problems.append("duplicate construction_workitems ids")
    known_refs = known_refs | set(cw_ids)
    for it in zones.get("construction_workitems", []):
        iid = it.get("id", "?")
        if it.get("zone", "construction") != "construction":
            problems.append(f"{iid}: construction_workitem must have zone=construction")
        if it.get("owner") not in OWNER_ENUM:
            problems.append(f"{iid}: bad owner")
        if it.get("status") not in STATUS_ENUM:
            problems.append(f"{iid}: bad status {it.get('status')!r}")
        for b in it.get("blocks", []):
            if b not in known_refs:
                problems.append(f"{iid}: unknown blocker {b!r}")
        for x in it.get("external_inputs", []):
            if x not in known_refs:
                problems.append(f"{iid}: unknown external input {x!r}")

    # external inputs
    for x in zones.get("external_inputs", []):
        xid = x.get("id", "?")
        if x.get("zone") not in ZONE_ENUM:
            problems.append(f"{xid}: bad zone")
        if x.get("state") not in {"stated", "opaque", "unmodeled", "proved"}:
            problems.append(f"{xid}: bad state {x.get('state')!r}")
        hw = x.get("hard_workitem")
        if hw and hw not in set(item_ids) | set(cw_ids):
            problems.append(f"{xid}: unknown hard_workitem {hw!r}")

    # 6. module registry
    registered = {m.get("path") for m in zones.get("modules", [])}
    for m in zones.get("modules", []):
        p = ROOT / str(m.get("path", ""))
        if not p.exists():
            problems.append(f"module path missing: {m.get('path')}")
        if m.get("zone") not in ZONE_ENUM:
            problems.append(f"module {m.get('path')}: bad zone {m.get('zone')!r}")
        target = str(m.get("target", ""))
        z = m.get("zone")
        if z in TARGET_PREFIX and not target.startswith(TARGET_PREFIX[z]):
            problems.append(f"module {m.get('path')}: target {target!r} not under {TARGET_PREFIX[z]}")
    on_disk = {str(p.relative_to(ROOT)).replace("\\", "/") for p in LEAN_DIR.rglob("*.lean")}
    root_lean = ROOT / "Kakeya4.lean"
    if root_lean.exists():
        on_disk.add("Kakeya4.lean")
    unregistered = sorted(on_disk - registered)
    if unregistered:
        problems.append(f"unregistered Lean files: {unregistered}")
    ghost = sorted(registered - on_disk)
    if ghost:
        problems.append(f"registered but missing on disk: {ghost}")

    # 7. external-input mapping to dependency registry
    dep_ids = {d.get("id") for d in deps}
    statement_zone_expected = {
        "ext:graph-balog-szemeredi-gowers": ("re:graph-bsg", "construction"),
        "lem:weighted-planks": ("lem:weighted-planks", "construction"),
    }
    workitem_expected = {
        "ext:determinant-multilinear-kakeya": "H-002",
        "ext:restricted-triple-dot-product": "H-003",
        "ext:multiplicative-convolution": "H-004",
    }
    for did, (label, zone) in statement_zone_expected.items():
        if did not in dep_ids:
            problems.append(f"dependency registry missing {did}")
        elif zone_of.get(label) != zone:
            problems.append(f"dependency {did}: expected {label} in zone {zone}, got {zone_of.get(label)!r}")
    for did, iid in workitem_expected.items():
        if did not in dep_ids:
            problems.append(f"dependency registry missing {did}")
        elif iid not in set(item_ids):
            problems.append(f"dependency {did}: missing hard work item {iid}")
    gbs = [x for x in zones.get("external_inputs", []) if x.get("id") == "X-GBS"]
    if not gbs or gbs[0].get("zone") != "construction":
        problems.append("external input X-GBS must be in zone construction (manuscript proof exists, AI builds)")

    # 8. counts
    counts: dict[str, int] = {}
    for s in zones.get("statements", []):
        counts[s["zone"]] = counts.get(s["zone"], 0) + 1
    if problems:
        for p in problems:
            print("FAIL: " + p, file=sys.stderr)
        return 1
    declared = zones.get("counts", {})
    actual_counts = {
        "statements": len(actual),
        "foundation": counts.get("foundation", 0),
        "construction": counts.get("construction", 0),
        "hard": counts.get("hard", 0),
        "hard_workitems": len(item_ids),
        "construction_workitems": len(cw_ids),
        "external_inputs": len(ext_ids),
    }
    for k, v in actual_counts.items():
        if declared.get(k) is not None and declared.get(k) != v:
            problems.append(f"counts[{k}] declared {declared.get(k)} != actual {v}")
    if problems:
        for p in problems:
            print("FAIL: " + p, file=sys.stderr)
        return 1
    print("zone registry ok: " + ", ".join(f"{k}={v}" for k, v in sorted(actual_counts.items()))
          + f"; modules={len(registered)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
