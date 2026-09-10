#!/usr/bin/env python3
"""Machine-checked regression fixtures for the proof gate.

`reports/PROOF.md` claims that every way of breaking this repository listed in `DECLARED_MODES`
below fails the pipeline — some modes exercised by more than one run, hence `DECLARED_RUNS` — and
names the layer that catches each one. Until this script existed, that claim was a report of
something a person once did by hand — nothing in CI re-established it, so nothing stopped a
change from quietly removing a layer while the prose went on describing it. This script turns the
claim into a test that runs on every CI run.

## What is checked, per fixture

Not merely "the pipeline exits nonzero". A fixture that failed for an unrelated reason would
satisfy that and prove nothing, so each fixture declares the **exact exit status expected from
every stage** — `lake build`, the import invariant, the source policy, the environment audit,
`./scripts/check_axioms.sh` itself, and the hash manifest — plus the one layer that is *under
test* and a substring its output must contain. All of that has to match, or the fixture fails.
That is what makes this a test of the layer rather than a test of "something went wrong
somewhere".

The `gate` stage is there because every other stage runs a check *directly*, and the pipeline the
documents actually name is the shell script that wraps them. A wrapper that lost an exit status —
a dropped `$?`, a stray `|| true`, a reordered branch — would leave every individual stage
reporting exactly what it reports today while CI went green on a corrupted tree. So each fixture
also runs `./scripts/check_axioms.sh` on its corrupted copy and requires both the exit status and
the diagnostic line naming the layer that failed. Fixture 6b is the one that requires the gate to
*pass*: only the hash manifest is stale there, and the manifest is CI's own step rather than part
of the gate.

The environment audit is skipped (recorded as `-`) for a fixture whose `lake build` fails: with no
`.olean`s there is nothing for it to import, so its exit status would say nothing about the audit.

## How the working tree is kept clean

The working tree is never written to. Each fixture is applied to a **fresh copy** of the
repository in a system temporary directory (`.git`, `.lake` and `__pycache__` excluded), the whole
pipeline runs there, and the copy is removed in a `finally` block. The copy lives outside the
repository, so a fixture's `.lean` file cannot be picked up by `scripts/check_source_policy.py`'s
or `scripts/gen_proof_sha256.py`'s globs over the real root, cannot enter the hash manifest, and
cannot enter the built library.

That is the guarantee by construction. It is also checked, within a stated scope: this script
takes a SHA-256 snapshot of every file under the real repository root **except `.git/`, `.lake/`
and `__pycache__/`** — git metadata, build output and bytecode caches, none of them repository
content — before the first fixture and again after the last, and fails if a single byte, path,
addition or deletion differs among the files it hashes. The three exclusions are safe to leave out
rather than merely convenient: this runner never invokes git and never builds in the real tree, it
builds only in the copies. So "the runner left the repository's own files alone" is verified
rather than asserted; "it left the build directory alone" is a property of never having touched
it, not something this snapshot demonstrates.

## What checks this runner

Nothing here would notice `FIXTURES` being emptied — a loop over an empty list satisfies every
assertion in it — so that case is closed before the loop: `validate_roster()` requires the exact
declared identifiers, in order, without duplicates, each with a layer under test that is actually
declared to fail. See `DECLARED_RUNS` for what that does and does not buy.

Usage:
    regression_fixtures.py [--root DIR] [--verbose]   # exit 0 iff all fixtures behave as declared
"""
import argparse
import hashlib
import pathlib
import shutil
import subprocess
import sys
import tempfile

# One definition of the controlled area, shared with the two checks that walk the same tree.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from check_imports import EXCLUDED_DIRS as EXCLUDED  # noqa: E402

MODEL = "AhlProofs/Model.lean"
ROOT_MODULE_FILE = "AhlProofs.lean"

# The four forbidden lexemes are assembled rather than written out, so that this file stays
# readable next to `scripts/check_source_policy.py` without inviting the question of why a
# repository that bans them contains them. The policy scans `*.lean` only, so a literal spelling
# here would break nothing — this is for the reader, not for the checker.
PLACEHOLDER = "sor" + "ry"
ADMIT = "ad" + "mit"
WARN_OFF = "warningAsError" + " false"
SKIP_TC = "debug." + "skipKernelTC"

# Every lexeme `scripts/check_source_policy.py` forbids, each exercised by its own fixture below.
# Testing three of the four and calling the rule covered was a real gap: deleting the `admit`
# pattern from the policy used to leave this runner green.
FORBIDDEN_LEXEMES = [PLACEHOLDER, ADMIT, WARN_OFF, SKIP_TC]


def append(root: pathlib.Path, rel: str, text: str) -> None:
    p = root / rel
    p.write_text(p.read_text(encoding="utf-8") + text, encoding="utf-8")


def prepend(root: pathlib.Path, rel: str, text: str) -> None:
    p = root / rel
    p.write_text(text + p.read_text(encoding="utf-8"), encoding="utf-8")


def comment_lexeme(lexeme: str):
    """A fixture that writes a forbidden lexeme into an ordinary Lean line comment.

    Nothing else changes: the comment does not reach the elaborator, so `lake build` still
    succeeds, the environment audit still finds nothing, and the *only* thing standing between
    this tree and a green run is the source policy. That isolates one policy rule per fixture —
    and it is also the shape the policy claims to have, since the ban is documented as total,
    comments and string literals included.
    """
    def apply(root: pathlib.Path) -> None:
        append(root, MODEL, f"\n-- {lexeme}\n")
    return apply


def fixture_1(root: pathlib.Path) -> None:
    """A module the root module does not import."""
    (root / "AhlProofs" / "Extra.lean").write_text("axiom planted_bad : False\n", encoding="utf-8")


def fixture_2(root: pathlib.Path) -> None:
    """A declaration that never becomes a constant, under a locally relaxed build setting."""
    append(root, MODEL, f"\nset_option {WARN_OFF} in\nexample : False := {PLACEHOLDER}\n")


def fixture_3(root: pathlib.Path) -> None:
    """A theorem admitted with the kernel's re-typechecking locally disabled."""
    prepend(root, MODEL, "import Lean\n")
    append(root, MODEL, f"""
open Lean Elab Tactic Meta
set_option {SKIP_TC} true in
theorem probe_tc : False := by
  run_tac do
    let g ← getMainGoal
    g.assign (mkConst ``True.intro)
""")


def fixture_4(root: pathlib.Path) -> None:
    """An ordinary unfinished theorem."""
    append(root, MODEL, f"\ntheorem probe_incomplete : True := by {PLACEHOLDER}\n")


def fixture_5(root: pathlib.Path) -> None:
    """An axiom of this repository's own, at top level."""
    append(root, MODEL, "\naxiom probe_axiom : False\n")


def fixture_6(root: pathlib.Path) -> None:
    """A new file under AhlProofs/, with the manifest left stale."""
    (root / "AhlProofs" / "Fresh.lean").write_text("import AhlProofs.Model\n", encoding="utf-8")


def fixture_6b(root: pathlib.Path) -> None:
    """Fixture 6 with the new file also imported, isolating the manifest layer.

    Fixture 6 in its plain form trips the import invariant as well as the manifest check. This
    variant adds the missing `import` line, so the import invariant passes and the manifest check
    is the only thing left standing between the tree and a green run — which is how the claim
    that the two layers are independent, rather than one masking the other, is established.
    """
    fixture_6(root)
    p = root / ROOT_MODULE_FILE
    t = p.read_text(encoding="utf-8")
    marker = "import AhlProofs.Tree.Boundary\n"
    assert t.count(marker) == 1, "root module no longer has the expected import to anchor to"
    p.write_text(t.replace(marker, marker + "import AhlProofs.Fresh\n"), encoding="utf-8")


def fixture_8(root: pathlib.Path) -> None:
    """Audit tooling in a subdirectory of `scripts/`, with the manifest left stale.

    `scripts/gen_proof_sha256.py` documents itself as hashing *every* audit script. It used to
    discover them with `glob`, which reads one directory level, while the library was discovered
    with `rglob`. A script one directory down was therefore unhashed — silently outside the
    manifest the documents said covered it. One file per extension the manifest claims to cover,
    so the recursive walk is exercised for all three rather than for whichever one a single
    fixture happened to pick.
    """
    nested = root / "scripts" / "nested"
    nested.mkdir(parents=True, exist_ok=True)
    (nested / "helper.py").write_text("# nested audit helper\n", encoding="utf-8")
    (nested / "helper.sh").write_text("#!/bin/sh\n: nested audit helper\n", encoding="utf-8")


def drop_canonical_sentence(rel: str):
    """Remove the canonical scope sentence from one of the three documents.

    The sentence names the boundary — the order and identity of the workflow's steps are checked,
    what each step runs is not — and is required verbatim in `README.md`, `reports/PROOF.md` and
    `reports/TOOLCHAIN.md`. It exists because a promise once outlived the code that kept it: the
    command comparison was deleted, `reports/PROOF.md` was rewritten to say so, and the other two
    documents went on promising "the same procedure". One run per document, because the
    requirement is one claim entry per document and a single run would leave two of them
    unexercised.
    """
    def apply(root: pathlib.Path) -> None:
        import sys as _sys
        _sys.path.insert(0, str(root / "scripts"))
        for name in list(_sys.modules):
            if name == "check_doc_claims":
                del _sys.modules[name]
        from check_doc_claims import CANONICAL_SCOPE_SENTENCE as sentence
        doc = root / rel
        text = doc.read_text(encoding="utf-8")
        words = sentence.split()
        import re as _re
        pattern = _re.compile(r"\s+".join(_re.escape(w) for w in words))
        assert pattern.search(text), f"{rel} does not carry the canonical sentence to remove"
        doc.write_text(pattern.sub("(sentence removed)", text, count=1), encoding="utf-8")
    return apply


def edit_workflow(old: str, new: str):
    """A change to the workflow above the step level, or to a step's own fields.

    The step schema was closed at the wrong depth once (`if: false` beside `runs-on:` disables the
    whole job while every step-level check reports the steps are exactly right) and admitted the
    wrong thing once (`evil/checkout@<40 hex>` satisfied a check on the *form* of a pin). Both are
    exercised through this one factory.
    """
    def apply(root: pathlib.Path) -> None:
        wf = root / ".github" / "workflows" / "ci.yml"
        t = wf.read_text(encoding="utf-8")
        assert t.count(old) == 1, f"anchor {old!r} not found exactly once in the workflow"
        wf.write_text(t.replace(old, new), encoding="utf-8")
    return apply


def axiom_in_audit_file(root: pathlib.Path) -> None:
    """An `axiom` declared in `scripts/Audit.lean`, ahead of the audit's own evaluation.

    The audit filtered by *home module*, and a constant declared in the file being elaborated has
    no home module — so an axiom here passed the audit, passed the source policy (`axiom` is not
    one of its four lexemes) and passed the gate, while `README.md` said "no `axiom` declaration
    of our own". It is planted before the `#eval` because that is the boundary of what the check
    can see, and the boundary is stated where the claim is made.
    """
    audit = root / "scripts" / "Audit.lean"
    t = audit.read_text(encoding="utf-8")
    anchor = "#eval show MetaM Unit from do"
    assert t.count(anchor) == 1, "Audit.lean no longer has the evaluation to anchor to"
    audit.write_text(t.replace(anchor, "axiom smuggled_in_audit : False\n\n" + anchor),
                     encoding="utf-8")


def add_step_field(field: str):
    """A field added to a workflow step that the schema does not admit."""
    def apply(root: pathlib.Path) -> None:
        wf = root / ".github" / "workflows" / "ci.yml"
        t = wf.read_text(encoding="utf-8")
        anchor = "      - name: Regression fixtures (each must fail, and fail at its own layer)\n"
        assert t.count(anchor) == 1, "the workflow no longer has the step to anchor to"
        wf.write_text(t.replace(anchor, anchor + f"        {field}\n"), encoding="utf-8")
    return apply


def drop_fixed_file(root: pathlib.Path) -> None:
    """An entry removed from the hash manifest's mandatory list.

    `lake-manifest.json` carries none of the covered suffixes, so the coverage rule says nothing
    about it; before the two lists had to agree, dropping it here produced a shorter manifest and
    a green run.
    """
    gen = root / "scripts" / "gen_proof_sha256.py"
    t = gen.read_text(encoding="utf-8")
    anchor = '    "lake-manifest.json",\n'
    assert t.count(anchor) == 1, "gen_proof_sha256.py no longer lists lake-manifest.json"
    gen.write_text(t.replace(anchor, ""), encoding="utf-8")


def extra_platform_branch(root: pathlib.Path) -> None:
    """An additional platform branch in the published install script.

    Every required branch and the `*)` default stay in place, and the set of archives offered is
    unchanged — which is exactly why this passed before: the check asked whether the recorded
    platforms were covered, not whether anything else was. From here on FreeBSD/x86_64 is no
    longer refused; it silently receives a Linux build.
    """
    doc = root / "reports" / "TOOLCHAIN.md"
    t = doc.read_text(encoding="utf-8")
    anchor = "  Linux/x86_64)\n"
    assert t.count(anchor) == 1, "the install script no longer has the branch to anchor to"
    doc.write_text(
        t.replace(
            anchor,
            "  FreeBSD/x86_64)\n"
            "    ASSET=lean-4.31.0-linux.tar.zst\n"
            "    DIGEST=07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f\n"
            "    ;;\n" + anchor,
        ),
        encoding="utf-8",
    )


def stray_lean(rel: str, body: str):
    """A `.lean` file in a place no declared category covers.

    Three of these, because the failure they exercise turned up three times in three different
    directories: under the library but unimported, under `scripts/` where a non-recursive glob
    missed it, and finally in the repository root, where `axiom planted_at_root : False` passed
    every check there was. `scripts/check_imports.py` now classifies every `.lean` in the tree
    instead of walking chosen directories, and these fixtures are what keeps that true.
    """
    def apply(root: pathlib.Path) -> None:
        target = root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(body, encoding="utf-8")
    return apply


# Each entry: expected exit status per stage (None = the stage is not run), the layer under test,
# a substring that layer's output must contain, and — separately — the diagnostic the whole gate
# (`./scripts/check_axioms.sh`) must print when it is expected to fail. `regen_manifest` reruns
# `gen_proof_sha256.py > reports/PROOF.sha256` after applying the fixture, which neutralises the
# manifest layer so that the layer under test is demonstrably the one doing the work; fixtures
# where manifest staleness *is* the subject leave it stale.
#
# `mode` groups runs that exercise the same failure mode: 6 and 6b are one mode with different
# layers active, and 7a-7d are one mode — a forbidden lexeme in the sources — once per lexeme.
GATE_IMPORTS = "GATE FAILED - scripts/check_imports.py exited 1"
GATE_POLICY = "GATE FAILED - scripts/check_source_policy.py exited 1"
GATE_AUDIT = "AUDIT FAILED - lake env lean scripts/Audit.lean exited 1"

FIXTURES = [
    {
        "id": "1",
        "mode": "1",
        "title": "module outside the root module's import list",
        "apply": fixture_1,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 1, "policy": 0, "audit": 0, "gate": 1, "manifest": 0, "docs": None},
        "layer": "imports",
        "reason": "is not reachable by imports from AhlProofs.lean",
        "gate_reason": GATE_IMPORTS,
    },
    {
        "id": "2",
        "mode": "2",
        "title": "declaration storing no constant, under a locally relaxed build setting",
        "apply": fixture_2,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 0, "policy": 1, "audit": 0, "gate": 1, "manifest": 0, "docs": None},
        "layer": "policy",
        "reason": f"forbidden lexeme `{WARN_OFF}`",
        "gate_reason": GATE_POLICY,
    },
    {
        "id": "3",
        "mode": "3",
        "title": "kernel re-typechecking locally disabled",
        "apply": fixture_3,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 0, "policy": 1, "audit": 0, "gate": 1, "manifest": 0, "docs": None},
        "layer": "policy",
        "reason": f"forbidden lexeme `{SKIP_TC}`",
        "gate_reason": GATE_POLICY,
    },
    {
        "id": "4",
        "mode": "4",
        "title": "ordinary unfinished theorem",
        "apply": fixture_4,
        "regen_manifest": True,
        "expect": {"build": 1, "imports": 0, "policy": 1, "audit": None, "gate": 1,
                   "manifest": 0, "docs": None},
        "layer": "build",
        "reason": "declaration uses",
        "gate_reason": GATE_POLICY,
    },
    {
        "id": "5",
        "mode": "5",
        "title": "own axiom at top level",
        "apply": fixture_5,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 0, "policy": 0, "audit": 1, "gate": 1, "manifest": 0, "docs": None},
        "layer": "audit",
        "reason": "own axiom declaration(s)",
        "gate_reason": GATE_AUDIT,
    },
    {
        "id": "6",
        "mode": "6",
        "title": "new file under AhlProofs/, manifest left stale",
        "apply": fixture_6,
        "regen_manifest": False,
        "expect": {"build": 0, "imports": 1, "policy": 0, "audit": 0, "gate": 1, "manifest": 1, "docs": None},
        "layer": "manifest",
        "reason": "reports/PROOF.sha256 is stale",
        "gate_reason": GATE_IMPORTS,
    },
    {
        "id": "6b",
        "mode": "6",
        "title": "same file, imported — isolating the manifest layer from the import invariant",
        "apply": fixture_6b,
        "regen_manifest": False,
        "expect": {"build": 0, "imports": 0, "policy": 0, "audit": 0, "gate": 0, "manifest": 1, "docs": None},
        "layer": "manifest",
        "reason": "reports/PROOF.sha256 is stale",
        # The gate passes here, and must: the hash manifest is checked by CI as its own step and
        # is deliberately not part of ./scripts/check_axioms.sh. A fixture whose only failing
        # stage is the manifest is exactly how that separation gets demonstrated.
        "gate_reason": "",
    },
] + [
    {
        "id": f"7{suffix}",
        "mode": "7",
        "title": f"forbidden lexeme `{lexeme}` in a Lean comment",
        "apply": comment_lexeme(lexeme),
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 0, "policy": 1, "audit": 0, "gate": 1, "manifest": 0, "docs": None},
        "layer": "policy",
        "reason": f"forbidden lexeme `{lexeme}`",
        "gate_reason": GATE_POLICY,
    }
    for suffix, lexeme in zip("abcd", FORBIDDEN_LEXEMES)
] + [
    {
        "id": "8",
        "mode": "8",
        "title": "audit tooling in a scripts/ subdirectory, manifest left stale",
        "apply": fixture_8,
        "regen_manifest": False,
        "expect": {"build": 0, "imports": 0, "policy": 0, "audit": 0, "gate": 0, "manifest": 1, "docs": None},
        "layer": "manifest",
        "reason": [
            "reports/PROOF.sha256 is stale",
            "scripts/nested/helper.py",
            "scripts/nested/helper.sh",
        ],
        # Nothing the gate covers is broken here: the manifest is CI's own step, as in 6b.
        "gate_reason": "",
    },
] + [
    {
        "id": f"9{suffix}",
        "mode": "9",
        "title": f"Lean file at {rel}, outside every declared category",
        "apply": stray_lean(rel, body),
        "regen_manifest": False,
        "expect": {"build": 0, "imports": 1, "policy": 0, "audit": 0, "gate": 1,
                   "manifest": manifest, "docs": None},
        "layer": "imports",
        "reason": [rel, "belongs to no declared category"],
        "gate_reason": GATE_IMPORTS,
    }
    for suffix, rel, body, manifest in [
        # The repository root: the case that passed every check there was.
        ("a", "Foo.lean", "axiom planted_at_root : False\n", 0),
        # Any other directory nothing walks.
        ("b", "docs/Notes.lean", "axiom planted_in_docs : False\n", 0),
        # Under scripts/, where the manifest does see it (rglob, fixture 8) but nothing classifies
        # it — so the manifest goes stale as well, and both layers are asserted.
        ("c", "scripts/nested/Helper.lean", "-- nested Lean helper\n", 1),
    ]
] + [
    {
        "id": f"10{suffix}",
        "mode": "10",
        "title": f"Lean file under {directory}/, a directory excluded from classification",
        "apply": stray_lean(f"{directory}/Bad.lean", "axiom hidden_from_coverage : False\n"),
        "regen_manifest": False,
        "expect": {"build": 0, "imports": 1, "policy": 0, "audit": 0, "gate": 1, "manifest": 0,
                   "docs": None},
        "layer": "imports",
        "reason": [f"{directory}/Bad.lean", "holds no repository source"],
        "gate_reason": GATE_IMPORTS,
    }
    for suffix, directory in [("a", ".git"), ("b", ".lake"), ("c", "__pycache__")]
] + [
    {
        "id": f"12{suffix}",
        "mode": "12",
        "title": f"{rel}, an executable artifact outside every declared category",
        "apply": stray_lean(rel, body),
        "regen_manifest": False,
        "expect": {"build": 0, "imports": 1, "policy": 0, "audit": 0, "gate": 1, "manifest": 0,
                   "docs": None},
        "layer": "imports",
        "reason": [rel, why],
        "gate_reason": GATE_IMPORTS,
    }
    for suffix, rel, body, why in [
        ("a", "tools/helper.py", "print('unhashed')\n", "outside scripts/"),
        ("b", "tools/helper.sh", "#!/bin/sh\n: unhashed\n", "outside scripts/"),
        ("c", ".github/workflows/extra.yml", "name: extra\non: push\n", "is not declared"),
    ]
] + [
    {
        "id": f"15{suffix}",
        "mode": "15",
        "title": f"`{field}` added to a workflow step",
        "apply": add_step_field(field),
        "regen_manifest": True,
        # Measure 0: a document-layer fixture needs no build, audit or gate of its own. The
        # docs stage builds the library itself and fails if that build fails, so build success is
        # still asserted; that the corruption is invisible to the source side is still asserted by
        # the imports, policy and manifest stages. This saves a cold build and a gate run per
        # document fixture.
        "expect": {"build": None, "imports": 0, "policy": 0, "audit": None, "gate": None,
                   "manifest": 0, "docs": 1},
        "layer": "docs",
        "reason": [needle, "schema does not admit"],
        "gate_reason": "",
    }
    for suffix, field, needle in [
        ("a", "if: false", "'if'"),
        ("b", "continue-on-error: true", "'continue-on-error'"),
        ("c", "shell: bash", "'shell'"),
    ]
] + [
    {
        "id": f"16{suffix}",
        "mode": "16",
        "title": title,
        "apply": edit_workflow(anchor, replacement),
        "regen_manifest": True,
        # Measure 0: a document-layer fixture needs no build, audit or gate of its own. The
        # docs stage builds the library itself and fails if that build fails, so build success is
        # still asserted; that the corruption is invisible to the source side is still asserted by
        # the imports, policy and manifest stages. This saves a cold build and a gate run per
        # document fixture.
        "expect": {"build": None, "imports": 0, "policy": 0, "audit": None, "gate": None,
                   "manifest": 0, "docs": 1},
        "layer": "docs",
        "reason": [needle],
        "gate_reason": "",
    }
    for suffix, title, anchor, replacement, needle in [
        ("a", "if: false on the job itself",
         "    runs-on: ubuntu-latest\n", "    if: false\n    runs-on: ubuntu-latest\n",
         "job `lean` declares ['if']"),
        ("b", "an undeclared job key",
         "    timeout-minutes: 25\n", "    timeout-minutes: 25\n    continue-on-error: true\n",
         "job `lean` declares ['continue-on-error']"),
        ("c", "an undeclared top-level workflow key",
         "jobs:\n", "permissions: write-all\n\njobs:\n",
         "top-level key(s) ['permissions']"),
        ("d", "a different runner image",
         "runs-on: ubuntu-latest", "runs-on: self-hosted",
         "runs on 'self-hosted', not the declared 'ubuntu-latest'"),
    ]
] + [
    {
        "id": "17",
        "mode": "17",
        "title": "the checkout action replaced by another repository, pin still well formed",
        "apply": edit_workflow(
            "uses: actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1",
            "uses: evil/checkout@0000000000000000000000000000000000000000"),
        "regen_manifest": True,
        "expect": {"build": None, "imports": 0, "policy": 0, "audit": None, "gate": None,
                   "manifest": 0, "docs": 1},
        "layer": "docs",
        "reason": ["evil/checkout@", "not one of the declared actions"],
        "gate_reason": "",
    },
    {
        "id": "18",
        "mode": "18",
        "title": "an axiom declared in the audit file itself",
        "apply": axiom_in_audit_file,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 0, "policy": 0, "audit": 1, "gate": 1, "manifest": 0,
                   "docs": None},
        "layer": "audit",
        "reason": ["this audit file declares axiom(s) of its own", "smuggled_in_audit"],
        "gate_reason": GATE_AUDIT,
    },
] + [
    {
        "id": f"19{suffix}",
        "mode": "19",
        "title": title,
        "apply": edit_workflow(anchor, replacement),
        "regen_manifest": True,
        "expect": {"build": None, "imports": 0, "policy": 0, "audit": None, "gate": None,
                   "manifest": 0, "docs": 1},
        "layer": "docs",
        "reason": [needle],
        "gate_reason": "",
    }
    for suffix, title, anchor, replacement, needle in [
        ("a", "a duplicate top-level key", "name: ci\n", "name: ci\nname: ci\n",
         "duplicate top-level key 'name'"),
        ("b", "a duplicate key on a step",
         "        run: ./scripts/check_axioms.sh\n",
         "        run: ./scripts/check_axioms.sh\n        run: echo nothing\n",
         "declares 'run' twice"),
        ("c", "a tab in place of indentation", "  lean:\n", "\tlean:\n",
         "tab character(s) on line"),
    ]
] + [
    {
        "id": f"20{suffix}",
        "mode": "20",
        "title": f"the canonical scope sentence removed from {rel}",
        "apply": drop_canonical_sentence(rel),
        "regen_manifest": False,
        "expect": {"build": None, "imports": 0, "policy": 0, "audit": None, "gate": None,
                   "manifest": 0, "docs": 1},
        "layer": "docs",
        "reason": [rel, "the canonical scope disclaimer"],
        "gate_reason": "",
    }
    for suffix, rel in [
        ("a", "README.md"), ("b", "reports/PROOF.md"), ("c", "reports/TOOLCHAIN.md"),
    ]
] + [
    {
        "id": "14",
        "mode": "14",
        "title": "an entry removed from the manifest's mandatory file list",
        "apply": drop_fixed_file,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 1, "policy": 0, "audit": 0, "gate": 1, "manifest": 0,
                   "docs": None},
        "layer": "imports",
        "reason": ["FIXED_FILES is not the declared set", "lake-manifest.json"],
        "gate_reason": GATE_IMPORTS,
    },
    {
        "id": "11",
        "mode": "11",
        "title": "an extra platform branch in the published install script",
        "apply": extra_platform_branch,
        "regen_manifest": False,
        # Nothing in the sources changes, so every source-side stage passes and the manifest — which
        # does not hash the prose documents — is current. Only the document check can see this.
        # Measure 0: a document-layer fixture needs no build, audit or gate of its own. The
        # docs stage builds the library itself and fails if that build fails, so build success is
        # still asserted; that the corruption is invisible to the source side is still asserted by
        # the imports, policy and manifest stages. This saves a cold build and a gate run per
        # document fixture.
        "expect": {"build": None, "imports": 0, "policy": 0, "audit": None, "gate": None,
                   "manifest": 0, "docs": 1},
        "layer": "docs",
        "reason": ["FreeBSD/x86_64", "no longer refused"],
        "gate_reason": "",
    },
]

# `gate` is `./scripts/check_axioms.sh` itself, run on the corrupted copy. It is not a fourth
# layer: it re-runs the three below it. It is here because everything else in this file calls the
# individual checks directly, and a wrapper that stopped propagating their exit status — a lost
# `$?`, a stray `|| true`, a reordered `if` — would leave every individual stage reporting exactly
# what it reports now while CI went green on a broken tree. Fixtures that assert the individual
# stages prove the layers work; this stage proves the pipeline the documents actually name does.
# `docs` is scripts/check_doc_claims.py. It is declared `None` — not run — for every fixture but
# the one whose subject lives in a document rather than in the sources, because it rebuilds the
# library and re-runs the gate, and paying that per fixture would triple the suite for no
# information.
STAGES = ["build", "imports", "policy", "audit", "gate", "manifest", "docs"]

# The roster this runner is required to execute, declared separately from the fixtures themselves
# and checked against them before anything runs.
#
# Why this exists. Without it, emptying `FIXTURES` makes the loop below iterate zero times, every
# assertion vacuously hold, and the summary line report success over nothing — the same shape of
# defect as a static audit manifest that passes when truncated to empty, which is what the first
# version of this repository's gate was rejected for. A watchdog that can pass while watching
# nothing is not a watchdog. So: the exact identifiers, in order, with no duplicates and no
# additions, or this runner fails before it starts.
#
# What this does not fix. `DECLARED_RUNS` lives in the same file as `FIXTURES`, so someone editing
# both together still gets a green run. That is not closed here and cannot be, but it is made
# more expensive: `scripts/check_doc_claims.py` compares this roster against the fixture table
# published in reports/PROOF.md, so the same edit has to be made in three places, in one commit,
# to go unnoticed. See "Trust boundary" in reports/PROOF.md.
DECLARED_RUNS = ("1", "2", "3", "4", "5", "6", "6b", "7a", "7b", "7c", "7d", "8",
                 "9a", "9b", "9c", "10a", "10b", "10c", "12a", "12b", "12c",
                 "15a", "15b", "15c", "16a", "16b", "16c", "16d",
                 "17", "18", "19a", "19b", "19c", "20a", "20b", "20c", "14", "11")
DECLARED_MODES = ("1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "14",
                  "15", "16", "17", "18", "19", "20")
REQUIRED_KEYS = {
    "id", "mode", "title", "apply", "regen_manifest", "expect", "layer", "reason", "gate_reason",
}


def validate_roster() -> list[str]:
    """Structural checks on FIXTURES itself, run before any fixture does. Returns problems."""
    problems: list[str] = []
    if not FIXTURES:
        return ["FIXTURES is empty — a run that executes no fixture must never report success"]

    ids = [f.get("id") for f in FIXTURES]
    duplicates = sorted({i for i in ids if ids.count(i) > 1})
    if duplicates:
        problems.append(f"duplicate fixture id(s): {duplicates}")
    if tuple(ids) != DECLARED_RUNS:
        missing = [i for i in DECLARED_RUNS if i not in ids]
        extra = [i for i in ids if i not in DECLARED_RUNS]
        problems.append(
            f"fixture roster does not match the declared set: expected {list(DECLARED_RUNS)} in "
            f"that order, got {ids}"
            + (f"; missing {missing}" if missing else "")
            + (f"; unexpected {extra}" if extra else "")
        )

    modes = sorted({f.get("mode") for f in FIXTURES})
    if modes != sorted(DECLARED_MODES):
        problems.append(
            f"failure modes covered do not match the declared set: expected "
            f"{sorted(DECLARED_MODES)}, got {modes}"
        )

    for f in FIXTURES:
        fid = f.get("id", "<no id>")
        missing_keys = REQUIRED_KEYS - set(f)
        if missing_keys:
            problems.append(f"fixture {fid}: missing key(s) {sorted(missing_keys)}")
            continue
        if set(f["expect"]) != set(STAGES):
            problems.append(
                f"fixture {fid}: `expect` must give a value for every stage {STAGES}, got "
                f"{sorted(f['expect'])}"
            )
        if f["layer"] not in STAGES:
            problems.append(f"fixture {fid}: layer under test {f['layer']!r} is not a stage")
        elif f["expect"].get(f["layer"]) in (0, None):
            problems.append(
                f"fixture {fid}: layer under test `{f['layer']}` is not declared to fail, so the "
                "fixture would assert nothing about it"
            )
        reasons = f.get("reason", "")
        reasons = [reasons] if isinstance(reasons, str) else list(reasons)
        if not reasons or not all(str(r).strip() for r in reasons):
            problems.append(f"fixture {fid}: no expected reason substring for its layer")
        gate_expected = f["expect"].get("gate")
        gate_reason = str(f.get("gate_reason", "")).strip()
        if gate_expected not in (0, None) and not gate_reason:
            problems.append(
                f"fixture {fid}: the gate is declared to fail but no diagnostic is required of "
                "it — a fixture that accepts any nonzero exit from ./scripts/check_axioms.sh "
                "would not notice it failing for the wrong reason"
            )
        if gate_expected == 0 and gate_reason:
            problems.append(
                f"fixture {fid}: the gate is declared to pass but a diagnostic is required of it"
            )
    return problems

COMMANDS = {
    "build": ["lake", "build"],
    "gate": ["./scripts/check_axioms.sh"],
    "imports": [sys.executable, "scripts/check_imports.py"],
    "policy": [sys.executable, "scripts/check_source_policy.py"],
    "audit": ["lake", "env", "lean", "scripts/Audit.lean"],
    "manifest": [sys.executable, "scripts/gen_proof_sha256.py", "--check"],
    "docs": [sys.executable, "scripts/check_doc_claims.py"],
}


def run(cmd: list[str], cwd: pathlib.Path) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def snapshot(root: pathlib.Path) -> dict[str, str]:
    out: dict[str, str] = {}
    for p in sorted(root.rglob("*")):
        rel = p.relative_to(root)
        if EXCLUDED & set(rel.parts):
            continue
        if p.is_file():
            out[str(rel)] = hashlib.sha256(p.read_bytes()).hexdigest()
    return out


def copy_tree(root: pathlib.Path, dest: pathlib.Path) -> None:
    shutil.copytree(root, dest, ignore=shutil.ignore_patterns(*EXCLUDED), symlinks=True)


def run_fixture(spec: dict, root: pathlib.Path, verbose: bool) -> tuple[bool, dict, list[str]]:
    tmp = pathlib.Path(tempfile.mkdtemp(prefix=f"ahl-proofs-fixture-{spec['id']}-"))
    work = tmp / "repo"
    problems: list[str] = []
    actual: dict[str, int | None] = {}
    try:
        copy_tree(root, work)
        spec["apply"](work)
        if spec["regen_manifest"]:
            rc, out = run([sys.executable, "scripts/gen_proof_sha256.py"], work)
            if rc != 0:
                problems.append(f"could not regenerate the manifest in the copy: {out.strip()}")
                return False, actual, problems
            (work / "reports" / "PROOF.sha256").write_text(out, encoding="utf-8")

        outputs: dict[str, str] = {}
        for stage in STAGES:
            if spec["expect"][stage] is None:
                actual[stage] = None
                continue
            if stage == "audit" and actual.get("build") not in (0, None):
                actual[stage] = None
                problems.append(
                    "the audit stage was declared runnable but `lake build` failed, so its "
                    "result would say nothing about the audit"
                )
                continue
            rc, out = run(COMMANDS[stage], work)
            actual[stage], outputs[stage] = rc, out
            if verbose:
                print(f"    [{spec['id']}/{stage}] exit {rc}\n{out}", file=sys.stderr)

        for stage in STAGES:
            if actual.get(stage) != spec["expect"][stage]:
                problems.append(
                    f"stage `{stage}`: expected exit {spec['expect'][stage]}, got "
                    f"{actual.get(stage)}"
                )

        layer = spec["layer"]
        if spec["expect"][layer] in (0, None):
            problems.append(f"declaration error: layer under test `{layer}` is not expected to fail")
        if actual.get(layer) in (0, None):
            problems.append(
                f"the layer under test (`{layer}`) did not fail — a nonzero pipeline caused by "
                "some other stage does not count as this fixture passing"
            )
        else:
            wanted = spec["reason"]
            wanted = [wanted] if isinstance(wanted, str) else list(wanted)
            absent = [r for r in wanted if r not in outputs.get(layer, "")]
            if absent:
                problems.append(
                    f"layer `{layer}` failed but its output does not contain the expected "
                    f"reason(s) {absent!r}; got:\n{outputs.get(layer, '')[:1200]}"
                )

        # The gate as a whole, not just the layer inside it. Asserting only the individual
        # commands would leave ./scripts/check_axioms.sh free to swallow their exit status.
        gate_expected = spec["expect"].get("gate")
        if gate_expected not in (0, None):
            if actual.get("gate") in (0, None):
                problems.append(
                    "./scripts/check_axioms.sh exited "
                    f"{actual.get('gate')} on a tree that fails `{layer}` — the pipeline the "
                    "documents name did not break, whatever the individual commands report"
                )
            elif spec["gate_reason"] not in outputs.get("gate", ""):
                problems.append(
                    "./scripts/check_axioms.sh failed but did not print the expected diagnostic "
                    f"{spec['gate_reason']!r}; got:\n{outputs.get('gate', '')[-800:]}"
                )
        elif gate_expected == 0 and actual.get("gate") != 0:
            problems.append(
                f"./scripts/check_axioms.sh exited {actual.get('gate')} but this fixture leaves "
                "every layer it covers intact — only the hash manifest, which the gate does not "
                "check, is supposed to fail here"
            )

        if not any(rc not in (0, None) for rc in actual.values()):
            problems.append("the pipeline exited zero everywhere — this fixture must break it")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
        if tmp.exists():
            problems.append(f"temporary copy {tmp} could not be removed")
    return not problems, actual, problems


def render_table(rows: list[tuple[str, str, dict, bool]], hashed: int | None,
                 outcome: str) -> str:
    """The table of per-stage exit statuses, with a closing line that says how it was obtained.

    `outcome` is one of "declared", "passed" or "failed", and it decides that closing line —
    which is the whole point of the parameter. `--expected-table` renders the table from the
    *declarations* without executing anything, and it used to close with "behaved as declared:
    each broke the pipeline … Working tree unchanged", a sentence describing a run that had not
    happened. Nothing downstream was fooled — CI runs the fixtures in their own step — but a
    printed line that describes work not done is the same defect as a check that claims more than
    it establishes, and this repository has now produced that defect three times. So the declared
    rendering says it is declared, and only a real run may say a run behaved.

    Publishing the declared table is still sound: a run asserts actual == expected for every stage
    of every fixture and fails otherwise, so on any passing run the observed table *is* this one.
    """
    width = max(len(s) for s in STAGES)
    header = "  ".join(s.rjust(width) for s in STAGES)
    lines = [f"{'fixture':>8}  {'layer':>8}  {header}"]
    for fid, layer, actual, ok in rows:
        cells = "  ".join(
            ("-" if actual.get(s) is None else str(actual[s])).rjust(width) for s in STAGES
        )
        # No per-row verdict in the declared rendering: "ok" is a verdict, and in that mode
        # nothing has been run to reach one.
        verdict = "" if outcome == "declared" else ("   ok" if ok else "   FAILED")
        lines.append(f"{fid:>8}  {layer:>8}  {cells}{verdict}")
    lines.append("")
    excluded = ", ".join(sorted(f"{d}/" for d in EXCLUDED))
    if outcome == "declared":
        lines.append(
            f"declared outcomes for {len(DECLARED_RUNS)} fixture run(s) covering "
            f"{len(DECLARED_MODES)} failure mode(s). Nothing was executed to produce this table: "
            "it is rendered from the declarations, and a run is what checks them."
        )
    elif outcome == "passed":
        lines.append(
            f"all {len(DECLARED_RUNS)} fixture run(s) covering {len(DECLARED_MODES)} failure "
            "mode(s) behaved as declared: each broke the pipeline, and each was caught by the "
            f"layer named for it. Working tree unchanged ({hashed} file(s) hashed before and "
            f"after, excluding {excluded})."
        )
    else:
        failed = sum(1 for _, _, _, ok in rows if not ok)
        lines.append(
            f"FAILED: {failed} of {len(rows)} fixture run(s) did not behave as declared — see the "
            f"reasons above. Working tree unchanged ({hashed} file(s) hashed before and after, "
            f"excluding {excluded})."
        )
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".", help="repository root (default: cwd)")
    ap.add_argument("--verbose", action="store_true", help="print every stage's output")
    ap.add_argument(
        "--expected-table",
        action="store_true",
        help="print the report a passing run produces, without running the fixtures",
    )
    args = ap.parse_args()
    root = pathlib.Path(args.root).resolve()

    # Before anything else: is this runner about to run the fixtures it claims to run? A loop over
    # an empty or truncated list would satisfy every assertion below without executing anything.
    roster_problems = validate_roster()
    if roster_problems:
        print("regression_fixtures.py: FAIL — the fixture roster is not the declared one",
              file=sys.stderr)
        for problem in roster_problems:
            print(f"  - {problem}", file=sys.stderr)
        print(
            f"\nExpected exactly {list(DECLARED_RUNS)} covering failure modes "
            f"{list(DECLARED_MODES)}. A run that executes fewer fixtures than it claims must "
            "fail, not pass quietly.",
            file=sys.stderr,
        )
        return 1

    if args.expected_table:
        rows = [(f["id"], f["layer"], f["expect"], True) for f in FIXTURES]
        print(render_table(rows, None, outcome="declared"))
        return 0

    before = snapshot(root)
    if not before:
        print(f"FAIL: nothing found under {root}", file=sys.stderr)
        return 1

    # Fixtures that deliberately leave the manifest alone inherit whatever state the working tree
    # is in. If the baseline is already stale, their `manifest` stage fails for a reason that has
    # nothing to do with the fixture, and the run reports six confusing failures instead of one
    # clear one. Refuse to start rather than produce that.
    rc, out = run([sys.executable, "scripts/gen_proof_sha256.py", "--check"], root)
    if rc != 0:
        print("regression_fixtures.py: FAIL — the working tree's own manifest is stale, so "
              "fixture results would not be about the fixtures:\n" + out.strip(), file=sys.stderr)
        return 1

    rows: list[tuple[str, str, dict, bool]] = []
    failures: list[str] = []
    executed = 0
    for spec in FIXTURES:
        ok, actual, problems = run_fixture(spec, root, args.verbose)
        executed += 1
        rows.append((spec["id"], spec["layer"], actual, ok))
        if not ok:
            failures.append(
                f"fixture {spec['id']} ({spec['title']}):\n    - "
                + "\n    - ".join(problems)
            )

    if executed != len(DECLARED_RUNS):
        failures.append(
            f"{executed} fixture(s) ran but {len(DECLARED_RUNS)} were declared — a partial run "
            "must never be reported as a complete one"
        )

    after = snapshot(root)
    if before != after:
        changed = sorted(
            set(before) ^ set(after)
        ) + sorted(k for k in set(before) & set(after) if before[k] != after[k])
        failures.append(
            "the working tree changed while the fixtures ran — this runner must leave every file "
            "it hashes byte-for-byte identical: " + ", ".join(changed)
        )

    print(render_table(rows, len(before), outcome="passed" if not failures else "failed"))

    if failures:
        print("\nregression_fixtures.py: FAIL", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
