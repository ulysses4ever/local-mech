#!/usr/bin/env python3
"""
find_dead_code.py — Find unused definitions and lemmata in Rocq (.v) files.

Dead-code detection uses transitive closure via a reachability graph:

  1. Each tracked definition's "body" is the source text from its header up
     to the next tracked definition's header (or end of file).
  2. A uses-graph is built: uses[A] = set of tracked names mentioned in A's
     body (self-references excluded).
  3. Live roots are names that appear in the allowlist, or that are referenced
     from text outside all definition bodies (e.g. Require/Import preambles).
  4. All names reachable from live roots via the uses-graph are live.
  5. Everything else is reported as dead.

This means that if A is dead and B is only mentioned inside A, B is also
reported as dead — a single-pass occurrence-count approach would miss B.

Usage:
    python3 scripts/find_dead_code.py [--coqproject _CoqProject]
                                       [--allowlist FILE]
                                       [--error-on-dead]
                                       [--verbose]

Allowlist file format
---------------------
One name per line.  Lines starting with '#' and blank lines are ignored.
Names listed in the allowlist are excluded from the dead-code report.

Exit codes:
    0  — no (non-allowlisted) unused definitions found, or --error-on-dead
         not set
    1  — unused definitions found AND --error-on-dead was specified
    2  — usage/file error
"""

import re
import sys
import argparse
from pathlib import Path

# ---------------------------------------------------------------------------
# Keywords that introduce a named, top-level Rocq definition.
# Excluded intentionally:
#   Inductive / CoInductive / Variant / Record / Class / Instance
#     — constructor and field names are defined inline and harder to track;
#       the type name itself is almost always referenced in the code that
#       follows so false-dead-type reports would be noisy.
#   Notation / Tactic Notation
#     — syntax sugar; the "name" is often an operator or a string, not a
#       plain identifier.
#   Coercion
#     — registered with the type system; may not appear as a plain reference.
# ---------------------------------------------------------------------------
DEFINITION_KEYWORDS = [
    "Definition",
    "Lemma",
    "Theorem",
    "Fixpoint",
    "CoFixpoint",
    "Corollary",
    "Fact",
    "Remark",
    "Proposition",
    "Example",
    "Function",
]

_WORD_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")

_KWDS_RE = "|".join(re.escape(k) for k in DEFINITION_KEYWORDS)
DEF_RE = re.compile(
    r"(?:(?:Local|Global|Private)\s+)?(?:" + _KWDS_RE + r")\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)",
)

# ---------------------------------------------------------------------------
# Comment stripping
# ---------------------------------------------------------------------------

def strip_comments(text: str) -> str:
    """Remove Rocq (* ... *) comments (handles nesting). Preserves newlines."""
    result: list[str] = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if text[i : i + 2] == "(*":
            depth += 1
            i += 2
        elif text[i : i + 2] == "*)" and depth > 0:
            depth -= 1
            i += 2
        elif depth == 0:
            result.append(text[i])
            i += 1
        else:
            # Inside a comment: preserve newlines to keep line positions meaningful.
            if text[i] == "\n":
                result.append("\n")
            i += 1
    return "".join(result)


# ---------------------------------------------------------------------------
# _CoqProject parsing
# ---------------------------------------------------------------------------

def read_coqproject(coqproject_path: Path) -> list[Path]:
    """Return the list of .v source files from a _CoqProject file."""
    base = coqproject_path.parent
    files: list[Path] = []
    with open(coqproject_path, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if line.endswith(".v") and not line.startswith("-"):
                files.append(base / line)
    return files


# ---------------------------------------------------------------------------
# Core analysis
# ---------------------------------------------------------------------------

def extract_definitions(text: str) -> list[tuple[int, int, str, str]]:
    """
    Return (char_pos, line_number, name, keyword) for every top-level
    definition in *text* (which should already have comments stripped).
    """
    results: list[tuple[int, int, str, str]] = []
    for m in DEF_RE.finditer(text):
        raw = m.group(0)
        # Determine which keyword matched.
        for kw in DEFINITION_KEYWORDS:
            if re.search(r"\b" + re.escape(kw) + r"\b", raw):
                keyword = kw
                break
        else:
            keyword = "Definition"
        name = m.group(1)
        line_no = text[: m.start()].count("\n") + 1
        results.append((m.start(), line_no, name, keyword))
    return results


def read_allowlist(path: Path) -> set[str]:
    """Read a name-per-line allowlist file; ignore blank lines and comments."""
    allowed: set[str] = set()
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            name = line.split("#", 1)[0].strip()
            if name:
                allowed.add(name)
    return allowed


def find_dead_code(
    coqproject: Path,
    verbose: bool = False,
    allowlist: set[str] | None = None,
) -> list[tuple[str, int, str, str]]:
    """
    Analyse all .v files listed in *coqproject* and return a list of
    potentially unused definitions as (filename, line_no, name, keyword).

    Dead-code detection uses transitive closure: a definition is dead when it
    is unreachable from any live root via the uses-graph.  Live roots are
    names in *allowlist* and names referenced in text that lies outside all
    tracked definition bodies (e.g. Require/Import preambles).
    Names present in *allowlist* are excluded from the result.
    """
    if allowlist is None:
        allowlist = set()

    files = read_coqproject(coqproject)

    # Per-file stripped text and definitions.
    file_stripped: dict[str, str] = {}
    # name -> (short_filename, line_no, keyword) — last writer wins for duplicates
    all_defs: dict[str, tuple[str, int, str]] = {}
    # fname -> sorted list of (char_pos, line_no, name, keyword)
    file_defs: dict[str, list[tuple[int, int, str, str]]] = {}

    for path in files:
        if not path.exists():
            print(f"Warning: {path} not found", file=sys.stderr)
            continue
        raw = path.read_text(encoding="utf-8")
        stripped = strip_comments(raw)
        fname = path.name
        file_stripped[fname] = stripped
        defs = extract_definitions(stripped)
        file_defs[fname] = defs
        for _pos, line_no, name, kw in defs:
            all_defs[name] = (fname, line_no, kw)

    all_names: set[str] = set(all_defs.keys())

    # -----------------------------------------------------------------
    # Build body texts and collect external (non-definition) text.
    #
    # Each definition's "body" spans from its header to the start of the
    # next definition in the same file, or to the end of the file.
    # Text that precedes the first definition in a file is "external"
    # (Require, Import, Section headers, etc.).
    # -----------------------------------------------------------------
    body_texts: dict[str, str] = {}
    external_parts: list[str] = []

    for fname, stripped in file_stripped.items():
        defs = file_defs.get(fname, [])
        if not defs:
            external_parts.append(stripped)
            continue
        external_parts.append(stripped[: defs[0][0]])
        for i, (pos, _line_no, name, _kw) in enumerate(defs):
            end = defs[i + 1][0] if i + 1 < len(defs) else len(stripped)
            body_texts[name] = stripped[pos:end]

    external_text = "\n".join(external_parts)

    # -----------------------------------------------------------------
    # Build uses-graph: uses[A] = set of tracked names A's body mentions
    # (self-references excluded; they do not affect reachability).
    # -----------------------------------------------------------------
    uses: dict[str, set[str]] = {}
    for name, body in body_texts.items():
        words = set(_WORD_RE.findall(body))
        uses[name] = (words & all_names) - {name}

    # -----------------------------------------------------------------
    # BFS from live roots to determine all live (reachable) names.
    #
    # Live roots:
    #   1. Names in the allowlist.
    #   2. Names referenced from external text (outside any definition body).
    # -----------------------------------------------------------------
    external_refs = set(_WORD_RE.findall(external_text)) & all_names
    live: set[str] = (allowlist & all_names) | external_refs
    queue: list[str] = list(live)
    while queue:
        current = queue.pop()
        for dep in uses.get(current, ()):
            if dep not in live:
                live.add(dep)
                queue.append(dep)

    # -----------------------------------------------------------------
    # Report dead = tracked names not reachable from any live root.
    # -----------------------------------------------------------------
    dead: list[tuple[str, int, str, str]] = []
    for name, (fname, line_no, kw) in all_defs.items():
        if name in allowlist:
            if verbose:
                print(f"  {fname}:{line_no} {kw} {name!r:40s}  (allowlisted)")
            continue
        is_dead = name not in live
        if verbose:
            status = "DEAD" if is_dead else "live"
            print(f"  {fname}:{line_no} {kw} {name!r:40s}  ({status})")
        if is_dead:
            dead.append((fname, line_no, name, kw))

    return dead


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Find unused Rocq definitions and lemmata.",
    )
    parser.add_argument(
        "--coqproject",
        default="_CoqProject",
        metavar="FILE",
        help="Path to _CoqProject (default: _CoqProject)",
    )
    parser.add_argument(
        "--allowlist",
        metavar="FILE",
        help=(
            "Path to a file listing definition names (one per line) that "
            "should not be reported as dead.  Lines starting with '#' and "
            "blank lines are ignored."
        ),
    )
    parser.add_argument(
        "--error-on-dead",
        action="store_true",
        help="Exit with code 1 when unused definitions are found",
    )
    parser.add_argument(
        "--verbose",
        "-v",
        action="store_true",
        help="Print occurrence counts for every definition",
    )
    args = parser.parse_args()

    coqproject = Path(args.coqproject)
    if not coqproject.exists():
        print(f"Error: {coqproject} not found", file=sys.stderr)
        sys.exit(2)

    allowed: set[str] = set()
    if args.allowlist:
        allowlist_path = Path(args.allowlist)
        if not allowlist_path.exists():
            print(f"Error: allowlist file {allowlist_path} not found", file=sys.stderr)
            sys.exit(2)
        allowed = read_allowlist(allowlist_path)

    dead = find_dead_code(coqproject, verbose=args.verbose, allowlist=allowed)

    if dead:
        print(f"Found {len(dead)} potentially unused definition(s):\n")
        for fname, line_no, name, kw in sorted(dead):
            print(f"  {fname}:{line_no}: {kw} {name}")
        print()
        if args.error_on_dead:
            sys.exit(1)
    else:
        print("No unused definitions found.")


if __name__ == "__main__":
    main()
