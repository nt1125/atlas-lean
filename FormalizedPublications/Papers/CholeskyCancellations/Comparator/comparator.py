#!/usr/bin/env python3
"""Comparator: check the library against cholesky_cancellations_comparator.json
(statement of record).

Reads cholesky_cancellations_comparator.json, then:
  1. every named theorem resolves in the library (grep for its declaration);
  2. every named definition resolves in the library, and the challenge
     module (challenge_module + ".lean", the independent restatement with
     `sorry` proofs) exists;
  3. the axioms reported by `Comparator/axioms.lean` are a subset of
     permitted_axioms (no `sorryAx`: the JSON has no acknowledged holes,
     matching the model's field set);
  4. the comparator/formalization separation holds: `Formalization/`
     imports no comparator module, `Challenge.lean` imports only
     Mathlib/MathlibExt plus the companion `Definitions`, and
     `Definitions.lean` imports only Mathlib/MathlibExt.

Empty theorem_names passes vacuously (seed state, pre-scaffolding).
Exit 0 iff all checks pass. Run as `python3 Comparator/comparator.py` from
`FormalizedPublications/Papers/CholeskyCancellations/` (audit step 4 of the
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
COMPARATOR_MODULES = {"Challenge", "Definitions", "cholesky_cancellations_comparator"}


def fail(msg):
    print(f"COMPARATOR FAIL: {msg}")
    return 1


def _imports(path):
    mods = []
    for line in path.read_text().splitlines():
        mm = re.match(r"import\s+([A-Za-z0-9_.]+)", line.strip())
        if mm:
            mods.append(mm.group(1))
    return mods


def _is_mathlib_or_ext(mod):
    return (
        mod == "Mathlib"
        or mod.startswith("Mathlib.")
        or mod == "MathlibExt"
        or mod.startswith("MathlibExt.")
    )


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

    print("=== 4b. definition names resolve; challenge module present ===")
    challenge = ROOT / "Comparator" / (spec.get("challenge_module", "") + ".lean")
    if not challenge.exists():
        rc = fail(f"challenge module {challenge.name} missing") or 1
    else:
        print(f"  ok: challenge module {challenge.name} present")
    for full in spec.get("definition_names", []):
        rel = full.split(".", 1)[1] if "." in full else full
        hits = [
            p for p in LIB.rglob("*.lean")
            if re.search(
                rf"(def|abbrev|structure|inductive|class)\s+{re.escape(rel)}\b",
                p.read_text())
        ]
        if not hits:
            rc = fail(f"{full} resolves nowhere") or 1
        else:
            print(f"  ok: {full}")

    print("=== 4s. comparator/formalization separation ===")
    separation_ok = True
    for p in sorted(LIB.rglob("*.lean")):
        for mod in _imports(p):
            if mod in COMPARATOR_MODULES or mod.startswith("Comparator."):
                rc = fail(
                    f"{p.relative_to(ROOT)} imports comparator module {mod}"
                ) or 1
                separation_ok = False
    challenge_path = ROOT / "Comparator" / "Challenge.lean"
    if challenge_path.exists():
        for mod in _imports(challenge_path):
            if mod != "Definitions" and not _is_mathlib_or_ext(mod):
                rc = fail(f"Challenge.lean imports disallowed module {mod}") or 1
                separation_ok = False
    definitions_path = ROOT / "Comparator" / "Definitions.lean"
    if definitions_path.exists():
        for mod in _imports(definitions_path):
            if not _is_mathlib_or_ext(mod):
                rc = fail(f"Definitions.lean imports disallowed module {mod}") or 1
                separation_ok = False
    if separation_ok:
        print(
            "  ok: Formalization imports no comparator module; "
            "Challenge/Definitions stay on Mathlib/MathlibExt (+Definitions)"
        )

    print("=== 4c. axioms subset of permitted ===")
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
    allowed = set(permitted)
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
