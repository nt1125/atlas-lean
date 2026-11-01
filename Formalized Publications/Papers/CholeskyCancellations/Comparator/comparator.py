#!/usr/bin/env python3
"""Comparator: check the library against cholesky_cancellations_comparator.json
(statement of record).

Reads cholesky_cancellations_comparator.json, then:
  1. every named theorem resolves in the library (grep for its declaration);
  2. every acknowledged hole resolves;
  3. the axioms reported by `lake env lean Comparator/axioms.lean` are subset
     of permitted_axioms, plus `sorryAx` ONLY if acknowledged_holes is
     non-empty (soundness composition: the audit's hole-uniqueness pinning
     makes the sorryAx attribution sound).

Empty theorem_names passes vacuously (seed state, pre-scaffolding).
Exit 0 iff all checks pass. Run as `python3 Comparator/comparator.py` from
`Papers/CholeskyCancellations/` (audit step 4 of the original repository).

Note: this is the project's audit comparator (it checks the library against
the statement of record). It is not an independent restatement of the paper
in Lean; that Atlas-style comparator does not exist yet. Step 3 (axioms)
needs a Lake project at this root, which is not set up yet; until then it
reports "no axiom blocks parsed" and the script exits 1.
"""

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "Formalization"


def fail(msg):
    print(f"COMPARATOR FAIL: {msg}")
    return 1


def main():
    rc = 0
    spec = json.loads((ROOT / "Comparator" / "cholesky_cancellations_comparator.json").read_text())
    permitted = set(spec["permitted_axioms"])
    names = spec.get("theorem_names", [])

    print("=== 4a. theorem names resolve ===")
    if not names:
        print("  (seed state: no theorems named yet — fill at scaffolding)")
    for full in names:
        short = full.split(".")[-1]
        hits = [
            p for p in LIB.rglob("*.lean")
            if re.search(rf"(theorem|lemma)\s+{re.escape(short)}\b", p.read_text())
        ]
        if not hits:
            rc = fail(f"{full} resolves nowhere") or 1
        else:
            print(f"  ok: {full}")

    print("=== 4b. acknowledged holes resolve ===")
    for hole in spec.get("acknowledged_holes", []):
        short = hole["name"].split(".")[-1]
        hits = [
            p for p in LIB.rglob("*.lean")
            if re.search(rf"(theorem|lemma|def)\s+{re.escape(short)}\b", p.read_text())
        ]
        if not hits:
            rc = fail(f"hole {hole['name']} resolves nowhere") or 1
        else:
            print(f"  ok (acknowledged, {hole['status']}): {hole['name']}")

    print("=== 4c. axioms subset of permitted (+sorryAx iff holes acknowledged) ===")
    out = subprocess.run(
        ["lake", "env", "lean", "Comparator/axioms.lean"],
        capture_output=True, text=True, cwd=ROOT,
    ).stdout
    blocks = re.findall(
        r"'([^']+)' depends on axioms: \[(.*?)\]", out, re.DOTALL
    )
    if not blocks:
        if not names:
            print("  (seed state: nothing to check yet)")
            print(f"=== comparator finished (rc={rc}) ===")
            return rc
        print("  (no axiom blocks parsed — axioms.lean output unexpected)")
        return 1
    allow_sorry = bool(spec.get("acknowledged_holes"))
    allowed = set(permitted) | ({"sorryAx"} if allow_sorry else set())
    for name, axlist in blocks:
        found = {a.strip() for a in axlist.split(",") if a.strip()}
        exotic = found - allowed
        if exotic:
            rc = fail(f"{name} depends on exotic axioms: {sorted(exotic)}") or 1
        else:
            print(f"  ok: {name} ⊆ permitted")
    print(f"=== comparator finished (rc={rc}) ===")
    return rc


if __name__ == "__main__":
    sys.exit(main())
