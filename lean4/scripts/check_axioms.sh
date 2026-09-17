#!/usr/bin/env bash
# Fail if any audited theorem depends on anything but the three kernel axioms.
#
# `CLAUDE.md` forbids closing a goal with an axiom, `native_decide`, `unsafe` or floats.  Printing
# `#print axioms` (TSDPP/Audit.lean) only *reports* that; this script is what turns the report into
# a pass/fail gate, so the promise is enforced rather than asserted.
#
# Usage:  lean4/scripts/check_axioms.sh
set -euo pipefail

export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/.."


# `lake env lean` reads the *existing* oleans and will happily import a stale `TSDPP`.  Build the
# root module first, otherwise a newly added declaration reads as `unknownIdentifier` (trap P-15).
if ! lake build TSDPP >/dev/null 2>&1; then
  lake build TSDPP
  echo "FAIL: the root module does not build"
  exit 1
fi

out=$(lake env lean TSDPP/Audit.lean 2>&1) || { echo "$out"; echo "FAIL: Audit.lean did not elaborate"; exit 1; }

# An elaboration failure is never acceptable: it would silently turn an audit line into a no-op.
if printf '%s\n' "$out" | grep -q 'error'; then
  echo "$out"
  echo "FAIL: Audit.lean did not elaborate cleanly"
  exit 1
fi

# Every `#print axioms X` must be accounted for — but *not* by demanding a verdict line.  Lean
# prints nothing at all when the axiom set is **empty**, which is strictly stronger than depending
# on a subset of the three kernel axioms (e.g. `copyStep`, `copyStep_self`, `copyStep_other` are
# proved by `rfl` and mention no axiom).  So the check is name-level: every reported name must be
# one we asked about, and anything we asked about and got no report for is an empty axiom set.
declared=$(grep -c '^#print axioms' TSDPP/Audit.lean)
reported=$(printf '%s\n' "$out" | grep -c "depends on axioms" || true)
if ! printf '%s\n' "$out" | python -c '
import re, sys
names = [l.split("TSDPP.", 1)[1].strip() for l in open("TSDPP/Audit.lean")
         if l.startswith("#print axioms TSDPP.")]
# A declaration name may end in a prime: Lean treats `betaMeasure_Ici_chernoff` and the same name
# with a trailing prime as two distinct declarations.  A primed name is echoed with TWO consecutive
# quote characters before ` depends on axioms: [...]`, where an unprimed name has one.  The character
# class must therefore admit the quote character; it is spelled \x27 (the same character) so that this
# shell string needs no quoting gymnastics.  Without it the name is truncated at the prime and the
# declaration is misfiled as an "EMPTY axiom set" — a *wrong* verdict, not a missing one.  Latent
# until the first primed name was audited: four arrive with the BetaConcentration restatements.
#
# NB: this block is one bash single-quoted string, so an apostrophe ANYWHERE in these lines — even
# inside a comment — silently ends it and breaks the script.  Hence the wording above, and \x27 below.
seen = set(re.findall(r"'\''TSDPP\.([A-Za-z0-9_.\x27]+)'\'' depends on axioms", sys.stdin.read()))
unknown = sorted(seen - set(names))
if unknown:
    print(f"FAIL: verdicts for names not in Audit.lean: {unknown}")
    sys.exit(1)
empty = sorted(set(names) - seen)
print(f"     {len(names)} audited, {len(seen)} reported, {len(empty)} with an EMPTY axiom set: "
      + ", ".join(empty))
'; then
  echo "FAIL: Audit.lean and its output disagree"
  exit 1
fi

# No `sorry` anywhere in the report.
if printf '%s\n' "$out" | grep -q 'sorryAx'; then
  echo "$out"
  echo "FAIL: a declaration depends on sorryAx"
  exit 1
fi

# Nothing outside the three kernel axioms.  Membership, not string equality: a declaration that
# depends on `[propext, Quot.sound]` is *stronger* than one needing `Classical.choice` too, so a
# subset must pass (e.g. `copyStep_iterate`, which needs no choice).
if ! printf '%s\n' "$out" | python -c '
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = []
for line in sys.stdin:
    m = re.search(r"depends on axioms: \[(.*)\]", line)
    if not m:
        continue
    extra = {a.strip() for a in m.group(1).split(",") if a.strip()} - allowed
    if extra:
        bad.append((line.strip(), sorted(extra)))
for line, extra in bad:
    print(f"{line}   <- not allowed: {extra}")
sys.exit(1 if bad else 0)
'; then
  echo "FAIL: the above depend on axioms beyond propext / Classical.choice / Quot.sound"
  exit 1
fi

# Belt and braces: the forbidden constructs must not appear in the sources at all, *outside
# comments*.  Comments must be stripped first, and Lean block comments nest, so a regex is not
# enough — a naive grep flags the phrase "no `sorry`" in a module docstring.
if ! python scripts/scan_forbidden.py; then
  exit 1
fi

# Tree invariant: every `TSDPP/*.lean` must be reachable from the root module by `import`.  A file
# that is in the directory but outside the closure is compiled by nothing and, as far as
# `lake build` is concerned, does not exist.  This project has hit that hole four times
# (`KL`/`GammaMGF`, then `BetaGamma`, then the two promoted modules, then four quarantined ones),
# so it is gated rather than merely documented.
if ! python - <<'PY'
import os, re, sys

root, d = "TSDPP.lean", "TSDPP"
# Declared and under construction, but not yet wired into the root module.  Anything listed here
# is expected to disappear from this set when its card closes; it is an *exemption*, not a hiding
# place — an exemption that outlives its card is itself a defect.
#
# EMPTY, and it should stay that way.  The last entry, `TSDPP.BetaConcentration`, was the worst
# instance of the defect the paragraph above warns about: it was 600 lines with twelve public
# declarations, imported by nothing, so `lake build` never compiled it *and* `Audit.lean` — which
# imports only `TSDPP` — could not even resolve its names, leaving every declaration axiom-unaudited
# behind a green gate.  It is now imported by `TSDPP.lean`, and the coverage check below requires it
# to be represented in `Audit.lean`, so it needs no exemption and has none.
#
# The mechanism is kept because "declared but not yet importable" is a real state (trap P-54).  But
# note what an entry costs: a listed module is inside *no* closure, so the coverage check below
# cannot see it either — for that module this script checks only that it compiles, never that its
# declarations are audited.  That is the price of the state, not a licence to park modules here.
IN_FLIGHT = set()

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

# `TSDPP.Audit` is deliberately not imported from the root module (see its docstring): `#print
# axioms` is a command, not a declaration, so importing it would put audit output in every build.
orphans = sorted(m for m in mods
                 if m not in seen and m not in ("TSDPP", "TSDPP.Audit") and m not in IN_FLIGHT)
if orphans:
    print("FAIL: TSDPP modules outside the root import closure (compiled by nothing):")
    for m in orphans:
        print(f"      {mods[m]}")
    print("      Import them from TSDPP.lean, or quarantine them to Scratch/.")
    sys.exit(1)

# --- Audit coverage: every module in the closure must be REPRESENTED ---------------------------
# The orphan check above proves every `TSDPP/` module is *built*.  It says nothing about whether it
# is *audited*: `TSDPP/Audit.lean` is a hand-maintained list of `#print axioms` lines, and nothing
# tied it back to the tree.  Add a module to `TSDPP.lean` and forget `Audit.lean`, and every check
# above stays green while the new module's declarations are never axiom-checked — the `IN_FLIGHT`
# hole again, with the import added.  This check is the converse of the name check near the top of
# the script: there, every *reported* name must be one we asked about; here, every *imported* module
# must have been asked about.  (`TSDPP` and `TSDPP.Audit` are not in `seen`, so they are out of
# scope: the root module is an import list, and Audit is the audit.)
#
# A closure module passes if EITHER some audited declaration is declared in it, OR it is named in
# `NOTHING_TO_AUDIT`.  That allowlist is for modules with no declarations to audit, and it is checked
# in *both* directions — an entry outside the closure, or an entry whose module does have
# declarations, is a defect.  Same discipline as `IN_FLIGHT`, same reason: an exemption that
# outlives its justification is what hides the next hole.
NOTHING_TO_AUDIT = {
    # `import Mathlib` and nothing else — one line, zero declarations, so there is genuinely nothing
    # to audit.  This is an empty module, not a regex miss; the file would otherwise be reported
    # uncovered forever.  If a declaration is ever added here, the both-directions check below
    # fails and forces an audit line instead.
    "TSDPP.Basic",
}

# Top-level declarations, with `private`/`local`/modifier prefixes and @[attributes] peeled off.
# Every `TSDPP/` module is a flat `namespace TSDPP`, so a declaration `foo` is audited as
# `TSDPP.foo`.  A *nested* namespace would make the two sides disagree about spelling and the
# module is then reported UNCOVERED — a false red, but a loud one, which is the safe direction.
_DECL = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"((?:private|protected|noncomputable|partial|unsafe|nonrec|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)", re.M)

def _strip_comments(txt):
    """Lean block comments nest, so a regex is not enough (cf. `scripts/scan_forbidden.py`)."""
    out, depth, i = [], 0, 0
    while i < len(txt):
        if txt.startswith("/-", i):
            depth += 1
            i += 2
        elif txt.startswith("-/", i) and depth:
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif txt.startswith("--", i):
            j = txt.find("\n", i)
            i = len(txt) if j < 0 else j
        else:
            out.append(txt[i])
            i += 1
    return "".join(out)

def public_decls(path):
    if not os.path.exists(path):
        return set()
    names = set()
    with open(path, encoding="utf-8") as fh:
        src = fh.read()
    for mt in _DECL.finditer(_strip_comments(src)):
        # `private` and `local` declarations are file-scoped: their mangled names are not importable,
        # so `Audit.lean` cannot name them and they cannot count towards coverage.
        # (`group(1) or ""` — the modifier group is None, not "", when no modifier is present.)
        mods_txt = mt.group(1) or ""
        if "private" not in mods_txt and "local" not in mods_txt:
            names.add(mt.group(2))
    return names

audited_names = set()
with open("TSDPP/Audit.lean", encoding="utf-8") as fh:
    for line in fh:
        if line.startswith("#print axioms TSDPP."):
            audited_names.add(line.split("TSDPP.", 1)[1].strip())

decls_of = {m: public_decls(mods.get(m, "")) for m in seen}
covered = {m: sorted(audited_names & decls_of[m]) for m in seen}
uncovered = sorted(m for m in seen if not covered[m] and m not in NOTHING_TO_AUDIT)
if uncovered:
    print("FAIL: TSDPP module(s) in the root import closure with no axiom audit:")
    for m in uncovered:
        print(f"      {mods.get(m, m)}  ({len(decls_of[m])} public declaration(s), 0 audited)")
    print("      `TSDPP/Audit.lean` imports only `TSDPP`, so its `#print axioms` lines ARE the audit;")
    print("      a module absent from them is compiled but never axiom-checked.  For each public")
    print("      declaration add `#print axioms TSDPP.<name>`, or — if the module really has no")
    print("      declarations — add its name to NOTHING_TO_AUDIT in scripts/check_axioms.sh.")
    sys.exit(1)

allow_stale = sorted(m for m in NOTHING_TO_AUDIT if m not in seen)
if allow_stale:
    print("FAIL: NOTHING_TO_AUDIT names module(s) that are not in the root import closure:")
    for m in allow_stale:
        print(f"      {m}")
    print("      Either the module does not exist (stale exemption) or it is not imported from")
    print("      TSDPP.lean.  Exempting a module that is never built audits nothing.")
    sys.exit(1)

allow_wrong = sorted(m for m in NOTHING_TO_AUDIT if m in seen and decls_of[m])
if allow_wrong:
    print("FAIL: NOTHING_TO_AUDIT names module(s) that DO have declarations to audit:")
    for m in allow_wrong:
        print(f"      {mods.get(m, m)}  ({len(decls_of[m])} declaration(s), "
              f"e.g. {', '.join(sorted(decls_of[m])[:3])})")
    print("      'Nothing to audit' is a claim about the module, and this one has declarations.")
    print("      Add audit lines for them and delete the NOTHING_TO_AUDIT entry.")
    sys.exit(1)

exempt = sorted(m for m in mods if m in IN_FLIGHT)

# A stale exemption is itself a defect: it hides nothing today, but it will silently hide the next
# module to take that name, and it is the exact shape the comment above warns about.
missing = sorted(IN_FLIGHT - set(mods))
if missing:
    print("FAIL: IN_FLIGHT names module(s) that do not exist (stale exemption):")
    for m in missing:
        print(f"      {m}")
    print("      Remove them from IN_FLIGHT in scripts/check_axioms.sh.")
    sys.exit(1)

# An in-flight module is exempt from the *orphan* check — never from *compilation*.  The exemption
# means "declared, not yet wired into the root module"; it must not come to mean "declared,
# possibly broken".  Without this loop nothing in the tree ever compiles an in-flight module:
# `lake build TSDPP` walks only the root module's import closure, `Audit.lean` names only
# declarations that already exist inside that closure, and the forbidden-token scan reads *text*.
# So a module that does not compile at all trips none of the three (trap P-54, found by a peer
# session: this gate was green while `TSDPP/BetaConcentration.lean` had five hard errors).
if exempt:
    import subprocess

    # A *concurrent* `lake build` over the same build directory can make lake report
    # "object file '...' does not exist".  That is a race, not a defect in the module, and it must
    # be reported differently — otherwise this gate trains a "red, so re-run it" reflex, and the
    # next *genuine* red gets re-run until it is green.  Retried once; if it is still race-shaped
    # the verdict is INDETERMINATE, not a compile error.
    def is_race(s):
        return "object file" in s and "does not exist" in s

    failed, racy = [], []
    for m in exempt:
        r = subprocess.run(["lake", "build", m], capture_output=True, text=True)
        if r.returncode != 0:
            r = subprocess.run(["lake", "build", m], capture_output=True, text=True)
        if r.returncode != 0:
            (racy if is_race(r.stdout + r.stderr) else failed).append(m)
            print(r.stdout[-4000:])
            print(r.stderr[-4000:])
    if failed:
        print("FAIL: in-flight module(s) do not compile: " + ", ".join(failed))
        print("      `lake build TSDPP` does NOT cover these — they sit outside its import closure.")
        print("      This is expected *while* an agent is mid-edit; it is fatal at delivery.")
        sys.exit(1)
    if racy:
        print("INDETERMINATE: in-flight module(s) could not be verified: " + ", ".join(racy))
        print("      lake reported 'object file ... does not exist' on both attempts, which is the")
        print("      signature of a concurrent `lake build`, not of a broken module.  Re-run with")
        print("      no other build running.  This line is NOT a compile error and must not be")
        print("      cleared by re-running until it goes away.")
        sys.exit(2)

print("     tree invariant OK: every TSDPP/ module is reachable from TSDPP.lean"
      + (f"\n       in flight (exempt from the orphan check, but COMPILED): {', '.join(exempt)}"
         if exempt else ""))
print(f"     audit coverage OK: {sum(1 for m in seen if covered[m])}/{len(seen)} modules in the root"
      " import closure have at least one audited declaration"
      + (f"; declaration-free and allowlisted: {', '.join(sorted(NOTHING_TO_AUDIT))}"
         if NOTHING_TO_AUDIT else ""))
PY
then
  exit 1
fi

echo "OK: $declared declarations audited; each depends on nothing, or on a subset of"
echo "    {propext, Classical.choice, Quot.sound}"
