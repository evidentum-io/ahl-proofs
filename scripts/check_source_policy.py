#!/usr/bin/env python3
"""Source policy: a small set of lexemes that have no legitimate use in this repository is
rejected outright, in every `.lean` file this repository admits — which is every one the coverage
layer classifies, since a Lean file under `.git/`, `.lake/` or `__pycache__/` is refused there
before this scan is reached.

**This is a policy over source text, not a semantic check.** The semantic check is
`scripts/Audit.lean`, which walks the compiled `Lean.Environment` and computes real axiom
closures with `Lean.collectAxioms`; that is what establishes what the proofs actually depend on.
This file establishes nothing about meaning. It only refuses four spellings, and it exists
because each of them is a way to make the semantic check look clean while it is not:

* `sorry` / `admit` — Lean's placeholder proof terms. The environment audit catches them via the
  `sorryAx` axiom *whenever the declaration they sit in becomes a constant*. In an `example`,
  which is elaborated and discarded rather than stored in `env.constants`, it does not become a
  constant, so the audit has nothing to look at.
* `warningAsError false` — `lakefile.toml` sets `warningAsError = true` so that Lean's own
  `declaration uses 'sorry'` warning is a build failure. `set_option warningAsError false in …`
  turns that off for one declaration, locally, from inside the source file the setting is meant
  to police.
* `debug.skipKernelTC` — disables the kernel's re-typechecking of a declaration. A proof term
  admitted under it can be accepted with an axiom closure that is entirely clean: nothing is
  added to the closure, because nothing was checked. This one is invisible to the environment
  audit by construction, not by accident.

The ban is total: no allowlist of files, no allowlist of places, no exemption for comments or
string literals. That totality is the point — an exemption list is a place for the next
regression to hide — and it has a price worth stating plainly: **this checker does not parse
Lean.** It matches raw bytes, literally: each file is read with `read_bytes()` and the patterns
are `bytes` patterns, so a file that is not valid UTF-8 is still scanned rather than crashing the
run, and a file that cannot be read at all is reported as a policy failure rather than skipped.
(Only the *display* of a matching line decodes, with `errors="replace"`, and only after the
finding has already been recorded. For the same reason the column in a finding is a byte offset
within the line, which differs from an editor's column on a line containing multi-byte
characters.) Prose inside a `.lean` file therefore cannot spell these
tokens either, and the doc comments in `scripts/Audit.lean` refer to Lean's placeholder terms
indirectly (`sorryAx`, "placeholder proof term") for exactly this reason. The alternative —
stripping comments before matching — would reintroduce the comment/string-literal parser whose
failure on a string literal containing `/-` is documented in `scripts/Audit.lean` as one of the
two proven blind spots of the audit this repository already retired. A parser that can be
confused is worse here than prose that has to be phrased around a word.

Discovery is a filesystem walk, not `git ls-files`: every `*.lean` in the working tree outside
`.git/`, `.lake/` and `__pycache__/` is scanned, which is a superset of the tracked files and does
not depend on whether a new file has been `git add`ed yet. Those three exclusions are shared with
`scripts/check_imports.py` (they are its `EXCLUDED_DIRS`, imported rather than repeated), and they
are not a way past this policy: that layer **refuses** a Lean file under any of them outright, so
a `.lean` this scan skips fails the gate one layer earlier.

Usage:
    check_source_policy.py [--root DIR]    # exit 0 if no forbidden lexeme occurs, 1 otherwise
"""
import argparse
import pathlib
import re
import sys

# One definition of the controlled area, imported rather than repeated. Three scripts walk this
# tree; when each carried its own copy they drifted — this one excluded `.git` and `.lake` but not
# `__pycache__`, so a `.lean` there was scanned by the policy and by nothing else. Sharing the
# constant removes the drift by construction instead of by another check.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from check_imports import EXCLUDED_DIRS, LEAN_SUFFIX  # noqa: E402

# (label, compiled pattern, why it is forbidden). Patterns are `bytes` patterns and run against
# the whole file, so a `set_option` split across lines is still matched, and a file that is not
# valid UTF-8 is scanned like any other instead of aborting the run.
FORBIDDEN = [
    (
        "sorry",
        re.compile(rb"\bsorry\b"),
        "Lean's placeholder proof term; inside an `example` it never becomes a constant, so the "
        "environment audit cannot see it",
    ),
    (
        "admit",
        re.compile(rb"\badmit\b"),
        "the tactic form of the same placeholder, with the same blind spot",
    ),
    (
        "warningAsError false",
        re.compile(rb"\bwarningAsError\b\s*(?::=)?\s*\bfalse\b"),
        "locally disables the `lakefile.toml` setting that makes Lean's "
        "`declaration uses 'sorry'` warning a build failure",
    ),
    (
        "debug.skipKernelTC",
        re.compile(rb"\bdebug\.skipKernelTC\b"),
        "disables kernel re-typechecking; a declaration admitted under it has a clean axiom "
        "closure because nothing was checked, so the environment audit reports nothing",
    ),
]


# The rules this policy is required to enforce, declared apart from the table above and checked
# against it before a single file is read.
#
# Same reasoning as `DECLARED_RUNS` in scripts/regression_fixtures.py and the mandatory-file check
# in scripts/gen_proof_sha256.py: `FORBIDDEN` is a list, and a loop over an empty or shortened list
# finds nothing and reports success over every file it read. Deleting one entry would then be a
# green run — which is precisely how the `admit` rule went untested for as long as it did. A
# checker built by iterating a table must refuse to run when the table is not the declared one.
DECLARED_LEXEMES = ("sorry", "admit", "warningAsError false", "debug.skipKernelTC")


def validate_rules() -> list[str]:
    problems: list[str] = []
    labels = [label for label, _, _ in FORBIDDEN]
    if not labels:
        return ["FORBIDDEN is empty — a policy that forbids nothing must not report compliance"]
    duplicates = sorted({x for x in labels if labels.count(x) > 1})
    if duplicates:
        problems.append(f"duplicate rule label(s): {duplicates}")
    if tuple(labels) != DECLARED_LEXEMES:
        problems.append(
            f"rule set does not match the declared one: expected {list(DECLARED_LEXEMES)} in that "
            f"order, got {labels}"
        )
    for label, pattern, why in FORBIDDEN:
        if not getattr(pattern, "pattern", None):
            problems.append(f"rule `{label}` has no pattern")
        elif not isinstance(pattern.pattern, bytes):
            problems.append(
                f"rule `{label}` is not a bytes pattern — this checker reads files as bytes, so a "
                "str pattern would raise rather than match"
            )
        if not str(why).strip():
            problems.append(f"rule `{label}` has no stated reason")
    return problems


def discover(root: pathlib.Path) -> list[pathlib.Path]:
    return sorted(
        p for p in root.rglob("*" + LEAN_SUFFIX)
        if p.is_file() and not p.is_symlink()
        and not (EXCLUDED_DIRS & set(p.relative_to(root).parts))
    )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".", help="repository root (default: cwd)")
    args = ap.parse_args()
    root = pathlib.Path(args.root).resolve()

    rule_problems = validate_rules()
    if rule_problems:
        print("check_source_policy.py: FAIL — the rule set is not the declared one",
              file=sys.stderr)
        for problem in rule_problems:
            print(f"  - {problem}", file=sys.stderr)
        print(
            f"\nExpected exactly {list(DECLARED_LEXEMES)}. A policy that enforces fewer rules "
            "than it claims must fail, not pass quietly.",
            file=sys.stderr,
        )
        return 1

    files = discover(root)
    if not files:
        print(f"FAIL: no .lean files found under {root} — refusing to report success on "
              "an empty scan", file=sys.stderr)
        return 1

    findings: list[str] = []
    for path in files:
        try:
            data = path.read_bytes()
        except OSError as e:
            # Fail closed: a .lean file this checker cannot read is a file the policy has not
            # been applied to, which must never be reported as compliance.
            findings.append(
                f"{path.relative_to(root)}: unreadable ({e}) — the policy cannot be applied to "
                "a file that cannot be read, and an unapplied policy is not a passing one"
            )
            continue
        # Precomputed line offsets, so a match anywhere in the file can be reported by position.
        starts = [0]
        for i, ch in enumerate(data):
            if ch == 0x0A:
                starts.append(i + 1)
        for label, pattern, why in FORBIDDEN:
            for m in pattern.finditer(data):
                lineno = 0
                lo, hi = 0, len(starts) - 1
                while lo <= hi:
                    mid = (lo + hi) // 2
                    if starts[mid] <= m.start():
                        lineno, lo = mid + 1, mid + 1
                    else:
                        hi = mid - 1
                col = m.start() - starts[lineno - 1] + 1
                raw_line = data[starts[lineno - 1]:].split(b"\n", 1)[0]
                line = raw_line.decode("utf-8", errors="replace")
                findings.append(
                    f"{path.relative_to(root)}:{lineno}:{col}: forbidden lexeme `{label}` "
                    f"({why})\n      {line.strip()}"
                )

    if findings:
        print("check_source_policy.py: FAIL — forbidden lexeme(s) in Lean sources",
              file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        print(
            "\nThe ban is total, with no allowlist: these four spellings have no legitimate use "
            "in this repository, in code or in prose. See this script's module docstring and "
            "\"Trust boundary\" in reports/PROOF.md.",
            file=sys.stderr,
        )
        return 1

    labels = ", ".join(f"`{label}`" for label, _, _ in FORBIDDEN)
    print(f"source policy holds: {len(files)} .lean file(s) scanned, none contains {labels}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
