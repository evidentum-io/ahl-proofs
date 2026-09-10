#!/usr/bin/env python3
"""Count every top-level `theorem`/`lemma` declaration in the AhlProofs library, for the
human-readable numbers quoted in `README.md` and `reports/PROOF.md` (currently 102).

**This script is not the axiom/`sorry` audit and its output is not an input to one.** That audit
is `scripts/Audit.lean`, which walks the *compiled* `Lean.Environment` after `import AhlProofs`
rather than parsing source text — see that file's module docstring for why: a text-based target
list, which is what an earlier version of this script produced for `scripts/check_axioms.sh`,
turned out to have two proven blind spots (a visibility modifier before `axiom`, and a string
literal containing `/-` confusing the comment-stripper below), both of which let a real `axiom`
or `sorry` through while this script still reported success. Discovering declarations by parsing
Lean source with regular expressions cannot be made complete — Lean's own grammar is not regular,
and this parser only approximates it — so this script's remaining job is narrower: produce a
*count* for prose, with a self-check that catches the parser missing something it should not
have (see below), not a completeness guarantee for anything security-relevant.

A raw `grep -rn "^theorem " AhlProofs | wc -l` both over- and under-counts: it matches prose
inside a `/-! ... -/` doc-comment block in `Closure/Boundary.lean` ("... and no theorem here
touches it.") and misses every `@[simp] theorem ...` declaration, since those lines do not start
with the bare keyword. This script strips comments first and recognises an attribute prefix, so
it does neither.

For each file it also reports (to stderr, or via --report) a self-check against silently missing
a declaration: a raw keyword count (occurrences of the words `theorem`/`lemma` anywhere in the
comment-stripped text) that must equal the number of declarations this script parsed out of that
file — a mismatch means some occurrence was not recognised as a clean top-level declaration (e.g.
an unusual indentation or a syntax this parser does not handle), and is treated as a parsing
blind spot for the *count*, not silently ignored. This is a weaker property than exhaustiveness:
it catches a keyword this parser fails to attribute to a declaration, but — as the two blind
spots above demonstrated — it says nothing about a declaration whose keyword this parser was
never looking for in the first place (`axiom`, `example`, any visibility-modified form). That is
exactly the gap `scripts/Audit.lean` closes by not parsing text at all.

Exit status is nonzero if that self-check fails, or if no files / no theorems were found at all
(an empty result must never look like "counted cleanly").
"""
import argparse
import pathlib
import re
import sys

KEYWORD_RE = re.compile(r"\b(?:theorem|lemma)\b")
NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z0-9_'.]+)\s*$")
SECTION_RE = re.compile(r"^section(?:\s+([A-Za-z0-9_'.]+))?\s*$")
END_RE = re.compile(r"^end(?:\s+([A-Za-z0-9_'.]+))?\s*$")
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z_][A-Za-z0-9_'!?]*)*)"
)


def discover_files(root: pathlib.Path) -> list[pathlib.Path]:
    files = []
    root_file = root / "AhlProofs.lean"
    if root_file.is_file():
        files.append(root_file)
    files += sorted((root / "AhlProofs").rglob("*.lean"))
    return files


def strip_comments(text: str) -> str:
    """Remove Lean block comments (`/- ... -/`, nesting included — this also removes doc
    comments `/-- ... -/` and module docs `/-! ... -/`, since both open with the two characters
    `/-`) and line comments (`-- ...` to end of line). Comments inside string literals are not
    handled specially; this codebase contains no string literal spanning `/-`, `-/` or `--`
    (checked by hand when this script was written), so a plain non-string-aware stripper is
    accurate here. A change that introduces such a literal would need this function revisited.
    """
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i:i + 2]
        if two == "/-":
            depth += 1
            i += 2
            continue
        if depth > 0:
            if two == "-/":
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if two == "--":
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        out.append(text[i])
        i += 1
    if depth != 0:
        raise ValueError("unbalanced block comment (depth %d at EOF)" % depth)
    return "".join(out)


def parse_file(path: pathlib.Path):
    """Returns (qualified_names, raw_keyword_count)."""
    stripped = strip_comments(path.read_text(encoding="utf-8"))
    stack: list[tuple[str, str | None]] = []
    names: list[str] = []
    raw_keyword_count = 0
    for lineno, line in enumerate(stripped.splitlines(), start=1):
        s = line.strip()
        if not s:
            continue
        m = NAMESPACE_RE.match(s)
        if m:
            stack.append(("namespace", m.group(1)))
            continue
        m = SECTION_RE.match(s)
        if m:
            stack.append(("section", m.group(1)))
            continue
        m = END_RE.match(s)
        if m:
            closer = m.group(1)
            if not stack:
                raise ValueError(f"{path}:{lineno}: 'end' with nothing open")
            kind, opener = stack.pop()
            if closer and opener and closer != opener:
                raise ValueError(
                    f"{path}:{lineno}: 'end {closer}' does not match open {kind} '{opener}'"
                )
            continue
        m = DECL_RE.match(s)
        if m:
            prefix = ".".join(n for k, n in stack if k == "namespace" and n)
            qualified = f"{prefix}.{m.group(1)}" if prefix else m.group(1)
            names.append(qualified)
        raw_keyword_count += len(KEYWORD_RE.findall(s))
    if stack:
        raise ValueError(f"{path}: unclosed {stack[-1][0]} {stack[-1][1]!r} at EOF")
    return names, raw_keyword_count


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".", help="repository root (default: cwd)")
    ap.add_argument(
        "--report", action="store_true", help="print per-file diagnostics to stderr"
    )
    args = ap.parse_args()
    root = pathlib.Path(args.root).resolve()

    files = discover_files(root)
    if not files:
        print(f"error: no .lean files discovered under {root}", file=sys.stderr)
        return 1

    all_names: list[str] = []
    problems: list[str] = []
    for f in files:
        rel = f.relative_to(root)
        try:
            names, raw_count = parse_file(f)
        except ValueError as e:
            problems.append(f"{rel}: parse error: {e}")
            continue
        if len(names) != raw_count:
            problems.append(
                f"{rel}: parsed {len(names)} declaration(s) but found {raw_count} "
                f"theorem/lemma keyword occurrence(s) in code — {raw_count - len(names)} "
                "unaccounted for (a blind spot in this count, not in the axiom/sorry audit, "
                "which does not use this script — see scripts/Audit.lean)"
            )
        if args.report:
            print(f"{rel}: {len(names)} theorem(s)", file=sys.stderr)
        all_names.extend(names)

    if problems:
        print("list_theorems.py: FAIL", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        return 1

    if not all_names:
        print("error: zero theorems discovered — this must never pass silently", file=sys.stderr)
        return 1

    for name in all_names:
        print(name)
    if args.report:
        print(f"total: {len(all_names)} theorem(s) in {len(files)} file(s)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
