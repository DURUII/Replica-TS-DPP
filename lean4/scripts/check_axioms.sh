#!/usr/bin/env bash
# Fail if any declaration in the `TSDPP` library depends on anything but the three kernel axioms.
#
# The axiom audit itself is delegated to `axiom-audit`
# (https://github.com/leanprover-community/axiom-audit, pinned in `lakefile.toml`).  It reads the
# compiled kernel environment rather than parsing `#print axioms` output, which makes it strictly
# stronger than the text audit this script used to carry: it sees axioms reached through imports and
# through `private` declarations, and it covers every declaration in the library instead of a
# hand-maintained list.  That is why the list, its name-accounting regex, and the
# audit-coverage / `NOTHING_TO_AUDIT` / `IN_FLIGHT` bookkeeping that existed only to keep the list
# honest are gone: there is no list left to drift.  `TSDPP/Audit.lean` is kept as the human-readable
# per-theorem report and as the record of the deliberation around it, but the gate no longer reads
# it.
#
# What an axiom audit structurally cannot see, and which therefore stays here as a source-level scan
# (`scripts/scan_forbidden.py`):
#   * `unsafe` definitions, which never appear as axioms in the environment;
#   * `opaque` with no value, an axiom in spirit but not registered as one;
#   * scratch files dropped into the deliverable directory.
# Measured on Lean v4.35.0-rc2 / axiom-audit 0b885d88: both constructs are reported "all within the
# allowlist", and are caught by the scan and only by the scan.
#
# The import-closure invariant is NOT delegated.  `lake exe mk_all --check` is not a substitute:
# `mk_all` walks every `.lean` under the directory with no per-file exclusion, so it would demand
# `import TSDPP.Audit` — the one import this project deliberately does not make.
#
# Usage:  lean4/scripts/check_axioms.sh
set -euo pipefail

export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.."

# `lake env` reads the *existing* oleans and will happily import a stale `TSDPP`.  Build the root
# module first: a newly added declaration otherwise reads as `unknownIdentifier` (trap P-15), and
# `axiom-audit` reconstructs the environment from those same oleans.
if ! lake build TSDPP >/dev/null 2>&1; then
  lake build TSDPP
  echo "FAIL: the root module does not build"
  exit 1
fi

# Kernel-environment audit of the whole `TSDPP` library, allowing only
# {propext, Classical.choice, Quot.sound}.  Exit 1 on any violation, and also when *nothing* was
# audited, so an empty audit cannot pass as a clean one.
if ! lake exe axiom-audit --root TSDPP; then
  echo "FAIL: the above depend on axioms beyond propext / Classical.choice / Quot.sound"
  exit 1
fi

# Source-level scan for the forbidden constructs the environment audit cannot see (see the header).
if ! python scripts/scan_forbidden.py; then
  exit 1
fi

# Import-closure invariant: every `TSDPP/*.lean` must be reachable from the root module by `import`.
# A file that is in the directory but outside the closure is compiled by nothing, so `lake build`
# and `axiom-audit` both never see it.  This project has hit that hole repeatedly (`KL`/`GammaMGF`,
# then `BetaGamma`, then the two promoted modules, then four quarantined ones, then
# `BetaConcentration` — 600 lines, twelve public declarations, imported by nothing), so it is gated
# rather than merely documented.  `TSDPP.Audit` is excluded on purpose: `#print axioms` is a command,
# not a declaration, so importing it would put audit output in every build.
if ! python - <<'PY'
import os, re, sys

root, d = "TSDPP.lean", "TSDPP"
imp = re.compile(r"^\s*(?:public\s+)?import\s+(TSDPP(?:\.[A-Za-z0-9_]+)*)\s*$", re.M)

def imports_of(path):
    if not os.path.exists(path):
        return set()
    with open(path, encoding="utf-8") as fh:
        return set(imp.findall(fh.read()))

mods = {f"TSDPP.{f[:-5]}": os.path.join(d, f) for f in os.listdir(d) if f.endswith(".lean")}
mods["TSDPP"] = root

seen, stack = set(), list(imports_of(root))
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    stack.extend(imports_of(mods.get(m, "")))

orphans = sorted(m for m in mods if m not in seen and m not in ("TSDPP", "TSDPP.Audit"))
if orphans:
    print("FAIL: TSDPP modules outside the root import closure (compiled by nothing):")
    for m in orphans:
        print(f"      {mods[m]}")
    print("      Import them from TSDPP.lean, or quarantine them to Scratch/.")
    sys.exit(1)
PY
then
  exit 1
fi

echo "OK: every declaration in the TSDPP library depends on nothing, or on a subset of"
echo "    {propext, Classical.choice, Quot.sound}; the import closure is complete."
