#!/usr/bin/env python3
"""Source policy: a small set of lexemes that have no legitimate use in this repository is
rejected outright, in every `.lean` file this repository admits — which is every one the coverage
layer classifies, since a Lean file under `.git/`, `.lake/` or `__pycache__/` is refused there
before this scan is reached.

**This is a policy over source text, not a semantic check.** The semantic check is
`scripts/Audit.lean`, which walks the compiled `Lean.Environment` and computes real axiom
closures with `Lean.collectAxioms`; that is what establishes what the proofs actually depend on.
This file establishes nothing about meaning. It refuses a short list of names, and it exists
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
  accepted under it carries an axiom closure that is entirely clean: nothing is added to the
  closure, because nothing was checked. This rule is now the *second* line of defence, not the
  first: `scripts/Audit.lean` re-adds every constant of the library to a kernel environment under
  an option set it builds itself, so a declaration that was never checked is caught semantically
  regardless of what any source file asked for. The rule stays because a cheap second net that
  fires earlier and reads plainly is worth keeping — but the guarantee no longer rests on it.

## Spellings, and why matching the literal name is not enough on its own

Lean lets any identifier be written between the quotation marks `«` and `»`, and the two
spellings are the same identifier: `set_option debug.skipKernelTC true` and
`set_option «debug».«skipKernelTC» true` do the same thing, and so do `warningAsError` and
`«warningAsError»`. A byte pattern for the unquoted name matches neither quoted form. This was not
hypothetical: a theorem of `False`, written under the quoted option, passed this policy and the
whole gate.

The fix is to stop matching one spelling: every file is matched **twice** — as it is on disk, and
again with the quoting characters removed — so a rule written for a name matches every spelling of
that name rather than one of them. A finding from the second pass says so, because its line and
column are positions in the rewritten copy rather than in the file.

Banning the two characters outright would have been cheaper, and was tried and rejected on
evidence: this repository uses them legitimately in two ways. They are the Russian quotation marks
in the doc comments that quote the invariants page, and `AhlProofs/Tree/Model.lean` genuinely needs
identifier quoting for the parameter `«from»`, because `from` is a Lean keyword. A rule that
forbade them would have demanded edits to the proofs to accommodate the checker, which is the wrong
direction.

The list of spellings a rule must catch is itself declared, in `MUST_REJECT`, and verified against
the rule table before any file is read — so this class of gap fails the run instead of passing it.

The honest boundary remains, and is smaller than it was: this layer refuses *names*, not
behaviour. It cannot know what a name does. What now knows is `scripts/Audit.lean`, which asks the
kernel again rather than trusting that the build asked.

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
tokens either, in any spelling, and the doc comments
in `scripts/Audit.lean` refer to Lean's placeholder terms indirectly (`sorryAx`, "placeholder proof
term") for exactly this reason. The alternative —
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
        "disables kernel re-typechecking; a declaration accepted under it has a clean axiom "
        "closure because nothing was checked. scripts/Audit.lean now re-checks every constant "
        "with the kernel regardless, so this rule is a second net rather than the guarantee",
    ),
]

# The rewriting applied before the second pass over each file: remove the identifier-quoting
# characters, so that a rule written for a name matches every spelling of that name. `«debug»`
# and `debug` are the same identifier to Lean; after this substitution they are the same bytes
# here. Reported separately from a plain match, because the position is a position in the
# rewritten text, not in the file.
IDENTIFIER_QUOTES = re.compile(rb"\xc2[\xab\xbb]")


# The rules this policy is required to enforce, declared apart from the table above and checked
# against it before a single file is read.
#
# Same reasoning as `DECLARED_RUNS` in scripts/regression_fixtures.py and the mandatory-file check
# in scripts/gen_proof_sha256.py: `FORBIDDEN` is a list, and a loop over an empty or shortened list
# finds nothing and reports success over every file it read. Deleting one entry would then be a
# green run — which is precisely how the `admit` rule went untested for as long as it did. A
# checker built by iterating a table must refuse to run when the table is not the declared one.
DECLARED_LEXEMES = ("sorry", "admit", "warningAsError false", "debug.skipKernelTC")


# Samples this policy is required to reject, checked against the rule table before any file is
# read. A pattern table is only as good as the spellings it was written against, and this
# repository has already been bitten once by exactly that gap: the rule for the kernel-typecheck
# option matched the plain name and not the identifier-quoted one, so a theorem of `False` written
# under the quoted spelling passed the whole gate. Declaring the samples turns "we believe the
# pattern covers this" into "the run refuses to start if it does not".
#
# Each entry is (sample bytes, the label that must fire). The quoted samples are written as escape
# sequences rather than literal characters so that this list stays legible as a list of spellings.
MUST_REJECT: tuple[tuple[bytes, str], ...] = (
    (b"  exact sorry\n", "sorry"),
    (b"  by admit\n", "admit"),
    (b"set_option warningAsError false in\n", "warningAsError false"),
    (b"set_option \xc2\xabwarningAsError\xc2\xbb false in\n", "warningAsError false"),
    (b"set_option debug.skipKernelTC true in\n", "debug.skipKernelTC"),
    (b"set_option \xc2\xabdebug\xc2\xbb.\xc2\xabskipKernelTC\xc2\xbb true in\n",
     "debug.skipKernelTC"),
    (b"set_option \xc2\xabdebug\xc2\xbb.skipKernelTC true in\n", "debug.skipKernelTC"),
)


def scan(data: bytes, location: str) -> list[tuple[str, str]]:
    """Match every rule against `data`, returning (label, finding) pairs.

    `location` is what a finding names — a path for the file as it is on disk, or that path plus a
    note for the pass over the rewritten copy, because the line and column of a match in the
    rewritten copy are positions in that copy and not in the file.
    """
    starts = [0]
    for i, ch in enumerate(data):
        if ch == 0x0A:
            starts.append(i + 1)
    out: list[tuple[str, str]] = []
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
            out.append((
                label,
                f"{location}:{lineno}:{col}: forbidden lexeme `{label}` ({why})\n      "
                f"{line.strip()}",
            ))
    return out


def scan_file(data: bytes, rel: str) -> list[tuple[str, str]]:
    """Both passes over one file's bytes: as read, then with the identifier-quoting characters
    removed. A label already reported by the first pass is not reported again by the second — the
    second pass exists to catch a spelling the first cannot see, not to double up on one it can.

    This is the **only** place the second pass is performed, and `validate_rules` checks the
    declared samples through this same function rather than repeating the rewrite. A first version
    did repeat it, and the consequence was immediate: disabling the second pass here left the
    sample check passing, so the guard could not fail for the defect it exists to catch.
    """
    raw = scan(data, rel)
    seen = {label for label, _ in raw}
    out = list(raw)
    normalized = IDENTIFIER_QUOTES.sub(b"", data)
    if normalized != data:
        note = f"{rel} (identifier-quoting characters removed before matching)"
        out += [(label, text) for label, text in scan(normalized, note) if label not in seen]
    return out


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
    if not isinstance(IDENTIFIER_QUOTES.pattern, bytes):
        problems.append(
            "IDENTIFIER_QUOTES is not a bytes pattern — the second pass rewrites file bytes"
        )
    if not MUST_REJECT:
        problems.append(
            "MUST_REJECT is empty — the rule table would then be checked against nothing"
        )
    for sample, expected in MUST_REJECT:
        labels_hit = {label for label, _ in scan_file(sample, "<MUST_REJECT sample>")}
        if expected not in labels_hit:
            problems.append(
                f"sample {sample!r} must be rejected by rule `{expected}`, but that rule did not "
                f"fire on it (rules that did: {sorted(labels_hit) or 'none'})"
            )
    return problems


def discover(root: pathlib.Path) -> list[pathlib.Path]:
    """Every `.lean` path this policy is responsible for, symbolic links **included**.

    Links used to be dropped here, next to directories and unreadable entries, as a kind of entry
    that could not carry source. That was wrong and it cost a green gate: `AhlProofs/Evil.lean ->
    ../Payload.txt` is compiled by Lake, skipped by this walk as a link, and never scanned under
    its target's name either, because `Payload.txt` does not end in `.lean`. They are returned now
    and refused by the caller — a refusal, not a scan of what they point at, because reading
    through a link would make this policy's own file list depend on something outside the tree.
    """
    return sorted(
        p for p in root.rglob("*" + LEAN_SUFFIX)
        if (p.is_file() or p.is_symlink())
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
            f"\nExpected exactly {list(DECLARED_LEXEMES)} as the rule set, and every declared "
            "sample rejected. A policy that enforces fewer rules than it claims — or fewer "
            "spellings of them — must fail, not pass quietly.",
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
        if path.is_symlink():
            findings.append(
                f"{path.relative_to(root)}: is a symbolic link. A `{LEAN_SUFFIX}` link is refused "
                "rather than followed: Lake compiles through one, and following it here would "
                "scan bytes that belong to whatever the link points at — possibly outside this "
                "repository — under the name of a file inside it. `scripts/check_imports.py` "
                "refuses every link one layer earlier; this is the same refusal, stated where "
                "the scan would otherwise have skipped it."
            )
            continue
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
        findings += [text for _, text in scan_file(data, str(path.relative_to(root)))]

    if findings:
        print("check_source_policy.py: FAIL — Lean source(s) this policy refuses",
              file=sys.stderr)
        for f in findings:
            print(f"  - {f}", file=sys.stderr)
        print(
            "\nThe ban is total, with no allowlist: these names have no legitimate use in this "
            "repository, in code or in prose, under any spelling — and a `.lean` that is a "
            "symbolic link is refused outright rather than scanned. See this script's module "
            "docstring and \"Trust boundary\" in reports/PROOF.md.",
            file=sys.stderr,
        )
        return 1

    labels = ", ".join(f"`{label}`" for label, _, _ in FORBIDDEN)
    print(
        f"source policy holds: {len(files)} .lean file(s), none a symbolic link, scanned twice "
        f"each — as read and with "
        f"identifier-quoting characters removed — none contains {labels}; the {len(MUST_REJECT)} "
        "declared must-reject sample(s) were all rejected before the scan began"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
