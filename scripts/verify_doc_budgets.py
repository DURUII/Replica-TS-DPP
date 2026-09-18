#!/usr/bin/env python
"""Word ceilings for accretion-prone standing docs.

Ported from deepseek-harness `scripts/verify-doc-budgets.ts` — the CI gate that repository
runs on its own documentation.  The doctrine is upstream's, verbatim from
`.agents/notes/implemented/process/2026-07-04-doc-tiers-and-budgets.md`:

    Its scope is deliberately only the accretion-prone standing docs ... Reference docs,
    Agent Notes, and complete package READMEs remain unbudgeted because exhaustive facts
    can be long.

    Ceilings are an enforcement frontier that ratchets.  A doc at or below its target keeps
    at least 5% headroom as its ceiling ratchets down; a doc above target keeps a frozen
    ceiling that prevents growth until it reaches the target.

and the ordered remedy, from upstream `docs/AGENTS.md`:

    1. Relocate content that belongs in another tier; leave a one-line link if needed.
    2. Condense content that belongs here but can be shorter.
    3. Raise the ceiling only when the words need the space; justify the manifest diff in
       the PR.  A too-low ceiling is a budget bug.

The honest reading of upstream's history is that such ceilings mostly ratchet *up*
(`AGENTS.md`: 1690 -> 1750 -> 1765 -> 1775 -> 1950).  That is not a failure mode: the value
is not that the gate pins a number, it is that **every growth becomes an explicit,
reviewable diff with a stated reason** instead of silent accretion.

## The counting rule is deliberately NOT `wc -w`

`wc -w` is locale-dependent and unusable on a corpus that mixes English and Chinese.  On this
machine (BSD `wc`, `LC_ALL=en_US.UTF-8`) it breaks inside multi-byte UTF-8 sequences at every
byte `0xA0`, so `a标b` counts as 2 words while `LC_ALL=C wc -w` counts it as 1; the same file
measures 61 or 72 words depending on the locale.  Measured 17/17 on a mixed probe set — see
DESIGN.md trap P-71.

We therefore use `len(text.split())`: a locale-independent count of Unicode-whitespace-
delimited tokens.  This is the same semantics as upstream's JS `text.split(/\\s+/).filter(Boolean)`.

    python scripts/verify_doc_budgets.py            # check; exit 1 on any violation
    python scripts/verify_doc_budgets.py --list     # report every row; never fails

Exit codes: 0 clean, 1 violations, 2 bad arguments.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MANIFEST = HERE / "doc_budgets.manifest.json"


def count_words(text: str) -> int:
    """Locale-independent `wc -w` equivalent; see the module docstring for why not `wc`."""
    return len(text.split())


def main(argv: list[str]) -> int:
    unknown = [arg for arg in argv if arg != "--list"]
    if unknown:
        print(f"verify-doc-budgets: unknown flag(s): {', '.join(unknown)}", file=sys.stderr)
        return 2
    list_mode = "--list" in argv

    if not MANIFEST.is_file():
        print(f"verify-doc-budgets: missing manifest at {MANIFEST}", file=sys.stderr)
        return 2
    budgets: dict[str, int] = json.loads(MANIFEST.read_text(encoding="utf-8"))

    rows: list[tuple[str, str, int | None, int]] = []
    failures: list[str] = []
    for rel, ceiling in budgets.items():
        path = ROOT / rel
        if not path.is_file():
            failures.append(
                f"{rel}: budgeted file does not exist "
                f"(renamed or deleted? update scripts/doc_budgets.manifest.json "
                f"in the same change)"
            )
            rows.append(("MISS", rel, None, ceiling))
            continue
        words = count_words(path.read_text(encoding="utf-8"))
        if words > ceiling:
            failures.append(
                f"{rel}: {words} words exceeds the {ceiling}-word ceiling — "
                f"relocate or condense (raising the ceiling requires justification in the PR)"
            )
            rows.append(("OVER", rel, words, ceiling))
        else:
            rows.append(("ok", rel, words, ceiling))

    if list_mode:
        for status, rel, words, ceiling in rows:
            shown = "-" if words is None else str(words)
            print(f"  {status:<5} {rel:<32} {shown:>7} / {ceiling}")
        over = sum(1 for r in rows if r[0] == "OVER")
        miss = sum(1 for r in rows if r[0] == "MISS")
        print(
            f"verify-doc-budgets: {len(rows) - over - miss} ok, "
            f"{over} over, {miss} missing (of {len(rows)} budgeted)"
        )
        return 0

    if failures:
        print(
            "verify-doc-budgets: word budgets violated "
            "(see deepseek-harness docs/AGENTS.md § Wordcount Budgets for the remedy order):",
            file=sys.stderr,
        )
        for failure in failures:
            print(f"  {failure}", file=sys.stderr)
        return 1

    print(f"verify-doc-budgets: OK ({len(rows)} budgeted files within their ceilings)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
