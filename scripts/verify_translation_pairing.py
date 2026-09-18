#!/usr/bin/env python
"""Bilingual-pair consistency gate for README files.

Ported from deepseek-harness `scripts/verify-translation-pairing.ts` (the CI gate that
repository runs over its own documentation corpus), narrowed to README files.  The unit is
a **three-file sibling triad** in the same directory:

    foo.md          the English side
    foo.zh.md       the Chinese side   -- both languages carry equal authority;
    foo.i18n.yaml   the consistency record   neither is designated the original

The record is the whole mechanism.  It holds, for each side, that file's **git blob SHA-1
as of the last confirmed-consistent state**.  Editing either side without bringing the
other along and re-recording makes the gate red:

    README.md: out of sync -- content no longer matches the pair's last confirmed-consistent
    state in README.i18n.yaml (bring the other side along, then re-record with --write)

There is **no skip marker, no ignore flag, and no "translation pending" state**: the only
acknowledgment is `--write <pair>`, and it requires having brought the other side along.
That is deliberate.  Upstream's own words: "a green gate means the pair was confirmed
consistent at these exact contents, not that the confirmation was sound."  Fidelity of the
translation itself is a review responsibility, not a machine one.

## What is checked

1. every in-scope README has both counterparts              (complete triad)
2. neither side has drifted from the recorded blob hashes   (staleness -- the core rule)
3. the record parses as exactly two `<basename>: <40-hex>` lines
4. an *excluded* path has no counterparts at all             (excluded means "must not exist")
5. each side links to the other right after its H1          (language switcher)
6. heading depths, code blocks, tables, lists and links agree across the pair
   (structural signature -- this is what a half-finished translation trips).  One entry per
   table, recorded as `rows x cols`, not one per table line.

## What is NOT checked

Per-side **length** is not compared, by design.  Upstream has no word-count, character-count
or length-ratio test anywhere in its pairing pipeline, and a half-translated file that keeps
the same headings, fences, tables, lists and links passes green.  Quantity fidelity is
explicitly left to review.  Doc *length* is a different gate -- see
`scripts/verify_doc_budgets.py`.

Nor is any **text** compared, except inside code fences.  The signature records a heading's
*depth*, a table's *shape*, a list's *indent* -- never its words.  Measured, so the boundary
is not hypothetical: renaming the Chinese side's `## DAG` to `## 依赖图`, re-recording so the
staleness check cannot mask it, still reports `OK`.  That is the intended scope (the skeleton
is machine-checkable; the prose is not), but it means a pair can be structurally consistent
and badly translated -- and green says nothing about which.  Code fences *are* byte-compared,
so an untranslated diagram is caught where a mistranslated sentence is not.

    python scripts/verify_translation_pairing.py                 # whole corpus; exit 1 on violation
    python scripts/verify_translation_pairing.py <pair>...       # only the named pairs
    python scripts/verify_translation_pairing.py --list          # report; never fails
    python scripts/verify_translation_pairing.py --write <pair>...  # re-record confirmed pairs
    python scripts/verify_translation_pairing.py --write --all

Any of a pair's three files, or its bare stem, names the same pair.  Exit codes: 0 clean,
1 violations, 2 bad arguments.

Differences from upstream, stated so they are not mistaken for parity:
  * the structural signature is computed by a line-based scanner, not by mdast;
  * `--cached` (git-index mode) is not implemented -- only the worktree is read;
  * the English-side switcher exemption list for generated sources is not carried.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
MANIFEST = HERE / "translation-pairing.manifest.json"

# In-scope corpus: README files at any depth, case-insensitively.  Upstream uses the same
# shape (`translation-pairing.ts`: `/(?:^|/)readme(?:\.md|\.zh\.md|\.i18n\.yaml)$/i`), which
# is why even a test fixture's README is paired there.
README_ARTIFACT = re.compile(r"(?:^|/)readme(?:\.md|\.zh\.md|\.i18n\.yaml)$", re.IGNORECASE)

# Dependency / generated / cache trees.  Upstream keeps two exemption layers: these glob
# excludes (mechanical, by location) and the manifest's `excluded` list (editorial, by file).
SCOPE_EXCLUDED_DIRS = {
    ".git", ".lake", ".npm-cache-local", "node_modules", "__pycache__", "pages",
    "vendor", "lib", ".cache", "coverage", "tmp", ".venv", "dist", "build",
}

SWITCHER = re.compile(r"^(?:English \| \[中文\]\([^\n]+\)|\[English\]\([^\n]+\) \| 中文)$")
RECORD_LINE = re.compile(r"^([^:#]+\.md): ([0-9a-f]{40})$")
FENCE = re.compile(r"^(\s*)(`{3,}|~{3,})(.*)$")
HEADING = re.compile(r"^(#{1,6})\s+(.*)$")
LIST_ITEM = re.compile(r"^(\s*)([-*+]|\d+[.)])\s+(.*)$")
LINK = re.compile(r"(?<!\!)\[([^\]]*)\]\(([^)\s]+)(?:\s+[^)]*)?\)")


# --------------------------------------------------------------------------- hashing

def git_blob_hash(data: bytes) -> str:
    """git blob SHA-1: sha1 over the real blob header ('blob <len>\\0') plus raw bytes."""
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def pair_paths(source: str) -> tuple[str, str, str]:
    if not source.endswith(".md") or source.endswith(".zh.md"):
        raise ValueError(f"expected an English Markdown path, received {source!r}")
    return source, source[:-3] + ".zh.md", source[:-3] + ".i18n.yaml"


def pair_anchor(argument: str) -> str:
    normalized = argument.replace("\\", "/").removeprefix("./")
    for suffix in (".zh.md", ".i18n.yaml"):
        if normalized.endswith(suffix):
            return normalized[: -len(suffix)] + ".md"
    return normalized if normalized.endswith(".md") else normalized + ".md"


# --------------------------------------------------------------------------- structure

def strip_fences(lines: list[str]) -> list[str]:
    """Drop fenced code -- tokens inside an example are not document structure."""
    out, fence = [], None
    for line in lines:
        m = FENCE.match(line)
        if fence is None and m:
            fence = m.group(2)[0]
            continue
        if fence is not None:
            if m and m.group(2)[0] == fence:
                fence = None
            continue
        out.append(line)
    return out


def switcher_line(lines: list[str]) -> str | None:
    """The switcher line -- a lone link paragraph right after the H1 -- or None."""
    seen_h1 = False
    for line in lines:
        if HEADING.match(line):
            if seen_h1:
                return None
            seen_h1 = True
            continue
        if seen_h1:
            if line.strip() == "":
                continue
            return line.strip() if SWITCHER.match(line.strip()) else None
    return None


def table_rows(rows: list[list[str]]) -> int:
    """A GFM delimiter row -- `| --- | :--: |` -- is not a row mdast reports."""
    return sum(
        1 for row in rows if not all(re.fullmatch(r":?-{3,}:?", c.strip()) for c in row)
    )


def signature(text: str) -> dict[str, list]:
    """Structural signature: heading depths, code blocks, tables, lists, links.

    The unit matches mdast, which is what upstream walks: one entry per *table*, recorded
    as `rows x cols`, not one per table *line*.  A 21-row table is one entry here.
    """
    lines = text.splitlines()
    skip = switcher_line(lines)
    prose = strip_fences(lines)
    sig: dict[str, list] = {"headings": [], "code": [], "tables": [], "lists": [], "links": []}

    # code blocks, verbatim (info string + body), from the *unstripped* text
    fence, info, body = None, "", []
    for line in lines:
        m = FENCE.match(line)
        if fence is None and m:
            fence, info, body = m.group(2)[0], m.group(3).strip(), []
        elif fence is not None:
            if m and m.group(2)[0] == fence:
                sig["code"].append(f"{info}\n" + "\n".join(body))
                fence = None
            else:
                body.append(line)

    # tables: consecutive `|`-starting lines form one table
    table: list[list[str]] = []

    def flush() -> None:
        if table:
            sig["tables"].append(f"{table_rows(table)}x{len(table[0])}")
            table.clear()

    for line in prose:
        if h := HEADING.match(line):
            sig["headings"].append(len(h.group(1)))
        if lst := LIST_ITEM.match(line):
            sig["lists"].append(f"indent{len(lst.group(1))}")
        if line.lstrip().startswith("|") and "|" in line:
            table.append(line.strip().strip("|").split("|"))
        else:
            flush()
        # the switcher links to the *other* language, so its target must differ by design
        if skip is None or line.strip() != skip:
            for m in LINK.finditer(line):
                sig["links"].append(m.group(2))
    flush()
    return sig


def signature_diff(source: str, zh: str) -> list[str]:
    a, b = signature(source), signature(zh)
    labels = {
        "headings": "heading (depth)",
        "code": "code block",
        "tables": "table (rows x cols)",
        "lists": "list (indent level)",
        "links": "link target",
    }
    out = []
    for field, label in labels.items():
        if a[field] != b[field]:
            n = min(len(a[field]), len(b[field]))
            where = next((i for i in range(n) if a[field][i] != b[field][i]), n)
            out.append(
                f"{label}: {len(a[field])} vs {len(b[field])} (first divergence at #{where + 1}: "
                f"{str(a[field][where] if where < len(a[field]) else '<none>')[:72]!r} vs "
                f"{str(b[field][where] if where < len(b[field]) else '<none>')[:72]!r})"
            )
    return out


# --------------------------------------------------------------------------- record

RECORD_HEADER = (
    "# Bilingual-pair consistency record: the git blob hash of each side as of the last\n"
    "# confirmed-consistent state.  Both languages carry equal authority; after editing\n"
    "# either side, bring the other along and re-record with:\n"
    "#   python scripts/verify_translation_pairing.py --write {anchor}\n"
)


def render_record(source: str, source_hash: str, zh: str, zh_hash: str) -> str:
    return (
        RECORD_HEADER.format(anchor=source)
        + f"{Path(source).name}: {source_hash}\n"
        + f"{Path(zh).name}: {zh_hash}\n"
    )


def parse_record(text: str, source: str, zh: str) -> tuple[str, str] | None:
    """Return (source_hash, zh_hash), or None if malformed.  Renamed/extra keys are malformed."""
    found: dict[str, str] = {}
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        m = RECORD_LINE.match(line.strip())
        if not m:
            return None
        found[m.group(1)] = m.group(2)
    if set(found) != {Path(source).name, Path(zh).name}:
        return None
    return found[Path(source).name], found[Path(zh).name]


# --------------------------------------------------------------------------- corpus

def load_manifest() -> list[str]:
    if not MANIFEST.is_file():
        return []
    data = json.loads(MANIFEST.read_text(encoding="utf-8"))
    unsupported = set(data) - {"excluded"}
    if unsupported:
        raise SystemExit(
            f"translation-pairing.manifest.json: unsupported field(s): "
            f"{', '.join(sorted(unsupported))}; only `excluded` is accepted"
        )
    return list(data.get("excluded", []))


def in_scope_dirs(rel: str) -> bool:
    return not any(part in SCOPE_EXCLUDED_DIRS for part in Path(rel).parts)


def is_excluded(rel: str, excluded: list[str]) -> bool:
    for entry in excluded:
        if entry.endswith("/"):
            if rel.startswith(entry):
                return True
        elif rel == entry:
            return True
    return False


def discover() -> list[str]:
    """In-scope README artifacts, with excluded trees *pruned* rather than walked.

    `Path.rglob` cannot prune, so it stats all 146_335 files under `lean4/.lake` (7.5 GB of
    vendored mathlib) before `in_scope_dirs` throws them away -- 7.4 s of the gate's 7.5 s.
    Pruning by directory name is exactly equivalent to filtering by `in_scope_dirs` after the
    fact, because that predicate also matches any path *component*.  Verified equivalent on
    this corpus: 2 hits either way.
    """
    hits = []
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = sorted(d for d in dirnames if d not in SCOPE_EXCLUDED_DIRS)
        for name in filenames:
            rel = (Path(dirpath) / name).relative_to(ROOT).as_posix()
            if README_ARTIFACT.search(rel):
                hits.append(rel)
    return sorted(hits)


def read(rel: str) -> bytes:
    return (ROOT / rel).read_bytes()


# --------------------------------------------------------------------------- gate

def check(anchors: list[str]) -> tuple[list[str], list[tuple[str, str]]]:
    """Return (errors, rows) where rows are (status, anchor) for --list."""
    excluded = load_manifest()
    errors: list[str] = []
    rows: list[tuple[str, str]] = []

    known = {r for r in discover() if not is_excluded(r, excluded)}
    if anchors:
        wanted = {pair_anchor(a) for a in anchors}
        unknown = sorted(wanted - known)
        for a in unknown:
            errors.append(
                f"{a} is not an in-scope pair (excluded, or its files are absent; "
                f"see scripts/translation-pairing.manifest.json)"
            )
        known = wanted & known

    # excluded paths must carry no counterparts
    for rel in discover():
        if not is_excluded(rel, excluded):
            continue
        for counterpart in (rel[:-3] + ".zh.md", rel[:-3] + ".i18n.yaml") if rel.endswith(".md") and not rel.endswith(".zh.md") else ():
            if (ROOT / counterpart).is_file():
                errors.append(
                    f"{counterpart}: {rel} is excluded from pairing; this artifact must not exist"
                )

    for source in sorted(known):
        if not source.endswith(".md") or source.endswith(".zh.md"):
            continue
        _source, zh, meta = pair_paths(source)
        have_zh, have_meta = (ROOT / zh).is_file(), (ROOT / meta).is_file()
        if not have_zh:
            errors.append(
                f"{source}: in-scope README must be paired; add {Path(zh).name} and record the pair"
            )
            rows.append(("missing", source))
            continue
        if not have_meta:
            errors.append(
                f"{source}: incomplete pair -- missing {Path(meta).name} "
                f"(pairs merge whole: both languages plus the record)"
            )
            rows.append(("missing", source))
            continue

        record = parse_record((ROOT / meta).read_text(encoding="utf-8"), source, zh)
        if record is None:
            errors.append(
                f"{meta}: malformed consistency record (expected exactly "
                f"`{Path(source).name}: <40-hex>` and `{Path(zh).name}: <40-hex>`)"
            )
            rows.append(("out-of-sync", source))
            continue

        source_bytes, zh_bytes = read(source), read(zh)
        rec_source, rec_zh = record
        drifted = False
        for rel, blob, recorded in ((source, source_bytes, rec_source), (zh, zh_bytes, rec_zh)):
            if git_blob_hash(blob) != recorded:
                errors.append(
                    f"{rel}: out of sync -- content no longer matches the pair's last "
                    f"confirmed-consistent state in {Path(meta).name} "
                    f"(bring the other side along, then re-record with --write)"
                )
                drifted = True
        if drifted:
            rows.append(("out-of-sync", source))
            continue

        source_text, zh_text = source_bytes.decode("utf-8"), zh_bytes.decode("utf-8")
        for rel, text, counterpart in ((zh, zh_text, Path(source).name), (source, source_text, Path(zh).name)):
            if f"]({counterpart})" not in text:
                errors.append(
                    f"{rel}: missing language switcher -- no link to {counterpart}"
                )
        for divergence in signature_diff(source_text, zh_text):
            errors.append(f"{source} <-> {zh}: {divergence}")

        rows.append(("ok", source))

    return errors, rows


def write_record(anchor: str, source_bytes: bytes, zh_bytes: bytes) -> None:
    source, zh, meta = pair_paths(anchor)
    (ROOT / meta).write_text(
        render_record(source, git_blob_hash(source_bytes), zh, git_blob_hash(zh_bytes)),
        encoding="utf-8",
    )


def main(argv: list[str]) -> int:
    list_mode, write_mode = "--list" in argv, "--write" in argv
    all_mode = "--all" in argv
    anchors = [a for a in argv if not a.startswith("--")]
    unknown = [a for a in argv if a.startswith("--") and a not in ("--list", "--write", "--all")]
    if unknown:
        print(f"verify-translation-pairing: unknown flag(s): {', '.join(unknown)}", file=sys.stderr)
        return 2
    if list_mode and (write_mode or anchors or all_mode):
        print("--list reports the whole corpus and takes no other flags or paths", file=sys.stderr)
        return 2
    if all_mode and not write_mode:
        print("--all only applies to --write", file=sys.stderr)
        return 2
    if write_mode and not all_mode and not anchors:
        print(
            "--write requires the pair(s) you confirmed (any file of a pair), or --all to "
            "re-record every complete pair; recording pairs you did not review blesses "
            "unconfirmed content",
            file=sys.stderr,
        )
        return 2
    if write_mode and all_mode and anchors:
        print("--write takes either pair paths or --all, not both", file=sys.stderr)
        return 2

    if list_mode:
        errors, rows = check([])
        order = {"out-of-sync": 0, "missing": 1, "ok": 2}
        for status, anchor in sorted(rows, key=lambda r: (order[r[0]], r[1])):
            print(f"  {status:<11} {anchor}")
        counts = {k: sum(1 for s, _ in rows if s == k) for k in order}
        print(
            f"verify-translation-pairing: {counts['ok']} ok, {counts['out-of-sync']} out-of-sync, "
            f"{counts['missing']} missing (of {len(rows)} in scope)"
        )
        return 0

    if write_mode:
        excluded = load_manifest()
        if all_mode:
            anchors = [
                r for r in discover()
                if r.endswith(".md") and not r.endswith(".zh.md") and not is_excluded(r, excluded)
            ]
        for anchor in anchors:
            source, zh, meta = pair_paths(pair_anchor(anchor))
            if not (ROOT / source).is_file() or not (ROOT / zh).is_file():
                print(f"{anchor} names no complete pair on disk", file=sys.stderr)
                return 2
            write_record(source, read(source), read(zh))
            print(f"  recorded {meta}")
        return 0

    errors, _ = check(anchors)
    if errors:
        print(
            "verify-translation-pairing: bilingual pairing rules violated:",
            file=sys.stderr,
        )
        for error in errors:
            print(f"  {error}", file=sys.stderr)
        return 1
    print("verify-translation-pairing: OK (every in-scope README is a consistent pair)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
