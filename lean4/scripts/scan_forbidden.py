#!/usr/bin/env python
"""Fail if `sorry`, `admit`, `native_decide` or `unsafe` appear in the Lean sources *as code*.

`CLAUDE.md` forbids closing a goal with an axiom, `native_decide`, `unsafe` or floats.  A plain
`grep` cannot enforce this: the words legitimately occur in docstrings (e.g. the module headers
say "no `sorry`, no `native_decide`"), and Lean block comments `/-- -/`, `/- -/` **nest**, so a
non-recursive stripper will mis-parse a file that documents a comment.

This strips comments with a depth counter, then scans what is left.  `Float` is deliberately not
scanned: it appears in prose and would be a constant source of false positives; the tokens below
have no legitimate use outside a comment or a string.

## Why `axiom` and `opaque` are in the list

`sorry` and `admit` are the *usual* way a goal is closed without a proof, but they are not the
only one, and the others are invisible to `#print axioms` in the following sense: `#print axioms`
reports on the declarations `Audit.lean` **lists**, so a declaration that nothing audited depends
on is never reported.  `axiom foo : P` placed in a file outside the root module's import closure
is therefore invisible to *all three* gates at once — this scan (token absent), `lake build` (file
never compiled), and the audit (nothing depends on `foo`).  `CLAUDE.md` names 公理 first in its
list of forbidden closers, so that is the one hole that must not exist.

`opaque c : T` with **no value** is exactly an axiom in Lean 4, and is caught by the same argument,
so it is scanned alongside.  (`opaque c : T := v` is harmless, and is not distinguished here —
over-rejecting is the correct direction for this gate.)

`partial def` is *not* scanned: it is a real escape hatch (nonterminating recursion compiles to
`implemented_by`), but `partial` is a common substring in Mathlib identifiers and the word-boundary
rule below still admits `partialOrder`-style names spelled with a lowercase `p`.  Recorded here as
a known, deliberate gap rather than silently omitted.

## Second check: no scratch files in the deliverable

`TSDPP/` is the artifact.  Exploratory files (`Probe5.lean`, `Scratch3.lean`, …) belong in
`../Scratch/`, which is *not* scanned — precisely so that a probe may use `sorry` and `#check`
freely while the deliverable stays clean.

This check exists because the two are easy to conflate and the failure is silent in the worst
way: a scratch file dropped into `TSDPP/` is picked up by the scan here but *not* by
`lake build` (it is outside the root module's import closure), so it is held to the `sorry`
rule without ever being type-checked.  Naming is the only signal available, so it is enforced.
"""

import re
import sys
from pathlib import Path

FORBIDDEN = ("sorry", "admit", "native_decide", "unsafe", "axiom", "opaque")
TOKEN = re.compile(r"(?<![A-Za-z0-9_'.])(%s)(?![A-Za-z0-9_'])" % "|".join(FORBIDDEN))

# Filename prefixes that mark a file as scratch.  Matched case-insensitively against the stem,
# so `tmp_foo.lean` and `TmpFoo.lean` are both caught.  Kept short on purpose: a prefix that is
# too aggressive would reject a legitimate deliverable, and the check is easier to trust when a
# human can verify the whole list at a glance.
SCRATCH_PREFIXES = ("probe", "scratch", "test", "tmp")


def strip_comments(src: str) -> str:
    """Remove `-- line` and nested `/- block -/` comments, preserving line numbers."""
    out = []
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            while i < n and src[i] != "\n":
                i += 1
        elif src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth > 0:
            out.append("\n" if src[i] == "\n" else " ")
            i += 1
        else:
            out.append(src[i])
            i += 1
    if depth != 0:
        raise ValueError("unterminated block comment")
    return "".join(out)


def main() -> int:
    root = Path(__file__).resolve().parent.parent / "TSDPP"
    # `rglob`, not `glob`: a file one level down (`TSDPP/sub/Foo.lean`) *is* in the `TSDPP` lean
    # library — Lake's default glob is `TSDPP.+` — so `lake build` compiles it.  Scanning only
    # the top level would leave exactly that file unscanned.  This cannot reach `../Scratch/`,
    # which is a sibling of `TSDPP/`, not a descendant.
    files = sorted(root.rglob("*.lean"))
    if not files:
        print(f"FAIL: no .lean files found under {root}")
        return 1

    failed = False

    stray = [p for p in files if p.stem.lower().startswith(SCRATCH_PREFIXES)]
    if stray:
        failed = True
        print("FAIL: scratch file in the deliverable directory (move it to `lean4/Scratch/`):")
        print("\n".join(f"  {p}" for p in stray))

    hits = []
    for path in files:
        # Audit.lean is a list of `#print axioms` commands; it contains no proof terms.
        if path.name == "Audit.lean":
            continue
        try:
            body = strip_comments(path.read_text())
        except ValueError as exc:
            print(f"FAIL: {path}: {exc}")
            return 1
        for lineno, line in enumerate(body.splitlines(), 1):
            for m in TOKEN.finditer(line):
                hits.append(f"{path}:{lineno}: {m.group(1)}  |  {line.strip()}")

    if hits:
        failed = True
        print("FAIL: forbidden construct found in source:")
        print("\n".join(hits))

    if failed:
        return 1

    print(f"OK: {len(files)} source files scanned, no {', '.join(FORBIDDEN)} in code")
    return 0


if __name__ == "__main__":
    sys.exit(main())
