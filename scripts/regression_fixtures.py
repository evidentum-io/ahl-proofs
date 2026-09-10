#!/usr/bin/env python3
"""Machine-checked regression fixtures for the proof gate.

`reports/PROOF.md` claims that 6 ways of breaking this repository each fail the pipeline (in 7
fixture runs — one mode is exercised twice, with different layers active), and
names the layer that catches each one. Until this script existed, that claim was a report of
something a person once did by hand — nothing in CI re-established it, so nothing stopped a
change from quietly removing a layer while the prose went on describing it. This script turns the
claim into a test that runs on every CI run.

## What is checked, per fixture

Not merely "the pipeline exits nonzero". A fixture that failed for an unrelated reason would
satisfy that and prove nothing, so each fixture declares the **exact exit status expected from
every stage** — `lake build`, the import invariant, the source policy, the environment audit, the
hash manifest — plus the one layer that is *under test* and a substring its output must contain.
All of that has to match, or the fixture fails. That is what makes this a test of the layer
rather than a test of "something went wrong somewhere".

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

EXCLUDED = {".git", ".lake", "__pycache__"}

MODEL = "AhlProofs/Model.lean"
ROOT_MODULE_FILE = "AhlProofs.lean"

# The four forbidden lexemes are assembled rather than written out, so that this file stays
# readable next to `scripts/check_source_policy.py` without inviting the question of why a
# repository that bans them contains them. The policy scans `*.lean` only, so a literal spelling
# here would break nothing — this is for the reader, not for the checker.
PLACEHOLDER = "sor" + "ry"
WARN_OFF = "warningAsError" + " false"
SKIP_TC = "debug." + "skipKernelTC"


def append(root: pathlib.Path, rel: str, text: str) -> None:
    p = root / rel
    p.write_text(p.read_text(encoding="utf-8") + text, encoding="utf-8")


def prepend(root: pathlib.Path, rel: str, text: str) -> None:
    p = root / rel
    p.write_text(text + p.read_text(encoding="utf-8"), encoding="utf-8")


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


# Each entry: expected exit status per stage (None = the stage is not run), the layer under test,
# and a substring that layer's output must contain. `regen_manifest` reruns
# `gen_proof_sha256.py > reports/PROOF.sha256` after applying the fixture, which neutralises the
# manifest layer so that the layer under test is demonstrably the one doing the work; fixtures
# where manifest staleness *is* the subject leave it stale.
FIXTURES = [
    {
        "id": "1",
        "mode": "1",
        "title": "module outside the root module's import list",
        "apply": fixture_1,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 1, "policy": 0, "audit": 0, "manifest": 0},
        "layer": "imports",
        "reason": "is not reachable by imports from AhlProofs.lean",
    },
    {
        "id": "2",
        "mode": "2",
        "title": "declaration storing no constant, under a locally relaxed build setting",
        "apply": fixture_2,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 0, "policy": 1, "audit": 0, "manifest": 0},
        "layer": "policy",
        "reason": f"forbidden lexeme `{WARN_OFF}`",
    },
    {
        "id": "3",
        "mode": "3",
        "title": "kernel re-typechecking locally disabled",
        "apply": fixture_3,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 0, "policy": 1, "audit": 0, "manifest": 0},
        "layer": "policy",
        "reason": f"forbidden lexeme `{SKIP_TC}`",
    },
    {
        "id": "4",
        "mode": "4",
        "title": "ordinary unfinished theorem",
        "apply": fixture_4,
        "regen_manifest": True,
        "expect": {"build": 1, "imports": 0, "policy": 1, "audit": None, "manifest": 0},
        "layer": "build",
        "reason": "declaration uses",
    },
    {
        "id": "5",
        "mode": "5",
        "title": "own axiom at top level",
        "apply": fixture_5,
        "regen_manifest": True,
        "expect": {"build": 0, "imports": 0, "policy": 0, "audit": 1, "manifest": 0},
        "layer": "audit",
        "reason": "own axiom declaration(s)",
    },
    {
        "id": "6",
        "mode": "6",
        "title": "new file under AhlProofs/, manifest left stale",
        "apply": fixture_6,
        "regen_manifest": False,
        "expect": {"build": 0, "imports": 1, "policy": 0, "audit": 0, "manifest": 1},
        "layer": "manifest",
        "reason": "reports/PROOF.sha256 is stale",
    },
    {
        "id": "6b",
        "mode": "6",
        "title": "same file, imported — isolating the manifest layer from the import invariant",
        "apply": fixture_6b,
        "regen_manifest": False,
        "expect": {"build": 0, "imports": 0, "policy": 0, "audit": 0, "manifest": 1},
        "layer": "manifest",
        "reason": "reports/PROOF.sha256 is stale",
    },
]

STAGES = ["build", "imports", "policy", "audit", "manifest"]

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
DECLARED_RUNS = ("1", "2", "3", "4", "5", "6", "6b")
DECLARED_MODES = ("1", "2", "3", "4", "5", "6")
REQUIRED_KEYS = {"id", "mode", "title", "apply", "regen_manifest", "expect", "layer", "reason"}


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
        if not str(f.get("reason", "")).strip():
            problems.append(f"fixture {fid}: no expected reason substring for its layer")
    return problems

COMMANDS = {
    "build": ["lake", "build"],
    "imports": [sys.executable, "scripts/check_imports.py"],
    "policy": [sys.executable, "scripts/check_source_policy.py"],
    "audit": ["lake", "env", "lean", "scripts/Audit.lean"],
    "manifest": [sys.executable, "scripts/gen_proof_sha256.py", "--check"],
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
        elif spec["reason"] not in outputs.get(layer, ""):
            problems.append(
                f"layer `{layer}` failed but its output does not contain the expected reason "
                f"{spec['reason']!r}; got:\n{outputs.get(layer, '')[:800]}"
            )

        if not any(rc not in (0, None) for rc in actual.values()):
            problems.append("the pipeline exited zero everywhere — this fixture must break it")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
        if tmp.exists():
            problems.append(f"temporary copy {tmp} could not be removed")
    return not problems, actual, problems


def render_table(rows: list[tuple[str, str, dict, bool]], hashed: int) -> str:
    """The runner's own report, in the exact form a passing run prints it.

    `--expected-table` renders this from the *declared* expectations without running anything, so
    a document can be checked against it cheaply (`scripts/check_doc_claims.py` does exactly
    that). That is sound only because a run asserts actual == expected for every stage of every
    fixture and fails otherwise: the expected table and the observed table are the same table on
    any run that succeeds, and on a run that does not succeed nothing is published.
    """
    width = max(len(s) for s in STAGES)
    header = "  ".join(s.rjust(width) for s in STAGES)
    lines = [f"{'fixture':>8}  {'layer':>8}  {header}"]
    for fid, layer, actual, ok in rows:
        cells = "  ".join(
            ("-" if actual.get(s) is None else str(actual[s])).rjust(width) for s in STAGES
        )
        lines.append(f"{fid:>8}  {layer:>8}  {cells}   {'ok' if ok else 'FAILED'}")
    lines.append("")
    lines.append(
        f"all {len(DECLARED_RUNS)} fixture run(s) covering {len(DECLARED_MODES)} failure mode(s) "
        "behaved as declared: each broke the pipeline, and each was caught by the layer named "
        f"for it. Working tree unchanged ({hashed} file(s) hashed before and after, excluding "
        + ", ".join(sorted(f"{d}/" for d in EXCLUDED))
        + ")."
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
        print(render_table(rows, len(snapshot(root))))
        return 0

    before = snapshot(root)
    if not before:
        print(f"FAIL: nothing found under {root}", file=sys.stderr)
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

    print(render_table(rows, len(before)))

    if failures:
        print("\nregression_fixtures.py: FAIL", file=sys.stderr)
        for f in failures:
            print(f"  - {f}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
