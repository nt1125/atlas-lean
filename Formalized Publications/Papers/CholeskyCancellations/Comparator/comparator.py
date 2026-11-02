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
`Formalized Publications/Papers/CholeskyCancellations/` (audit step 4 of the
original repository).

Step 3 (axioms) elaborates `Formalization/` into a temporary directory
(import-dependency order, bare `lean --root=Formalization` under the repo's
`lake env` search path), then runs `Comparator/axioms.lean` against those
oleans. This takes a few minutes and writes nothing into the repository.
"""

import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LIB = ROOT / "Formalization"


def fail(msg):
    print(f"COMPARATOR FAIL: {msg}")
    return 1


def _local_modules():
    mods = {}
    for p in sorted(LIB.rglob("*.lean")):
        mods[".".join(p.relative_to(LIB).with_suffix("").parts)] = p
    return mods


def _dependency_order(mods):
    order, state = [], {}

    def visit(m):
        if state.get(m) == 2:
            return
        if state.get(m) == 1:
            raise ValueError(f"import cycle at {m}")
        state[m] = 1
        for line in mods[m].read_text().splitlines():
            mm = re.match(r"import\s+([A-Za-z0-9_.]+)", line.strip())
            if mm and mm.group(1) in mods:
                visit(mm.group(1))
        state[m] = 2
        order.append(m)

    for m in mods:
        visit(m)
    return order


def _repo_root():
    """First ancestor of the project dir holding a lakefile (repo root)."""
    for cand in [ROOT, *ROOT.parents]:
        if (cand / "lakefile.toml").exists() or (cand / "lakefile.lean").exists():
            return cand
    return ROOT


def _lean_tool():
    out = subprocess.run(
        ["lake", "env", "sh", "-c", "command -v lean; printenv LEAN_PATH"],
        capture_output=True, text=True, cwd=_repo_root(),
    )
    lines = out.stdout.splitlines()
    if len(lines) < 2:
        return None, None
    return lines[0].strip(), lines[1].strip()


def _axioms_output():
    """Elaborate Formalization/ into a temp dir; return axioms.lean output."""
    lean_bin, lake_path = _lean_tool()
    if not lean_bin:
        print("  (could not resolve lean via `lake env`)")
        return None
    mods = _local_modules()
    try:
        order = _dependency_order(mods)
    except ValueError as e:
        print(f"  ({e})")
        return None
    tmp = tempfile.mkdtemp(prefix="comparator-oleans-")
    env = dict(os.environ)
    env["LEAN_PATH"] = tmp + ":" + lake_path
    for m in order:
        target = Path(tmp, *m.split(".")).with_suffix(".olean")
        target.parent.mkdir(parents=True, exist_ok=True)
        r = subprocess.run(
            [lean_bin, f"--root={LIB}", "-o", str(target), str(mods[m])],
            capture_output=True, text=True, env=env,
        )
        if r.returncode != 0:
            err = (r.stdout + r.stderr).splitlines()
            print(f"  (elaboration failed for {m}: "
                  f"{err[0] if err else 'no output'})")
            return None
    r = subprocess.run(
        [lean_bin, str(ROOT / "Comparator" / "axioms.lean")],
        capture_output=True, text=True, env=env,
    )
    return r.stdout + r.stderr


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
    out = _axioms_output()
    if out is None:
        return 1
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
