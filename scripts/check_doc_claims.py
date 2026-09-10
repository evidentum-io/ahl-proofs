#!/usr/bin/env python3
"""Tie the checkable claims in `README.md`, `reports/PROOF.md` and `reports/TOOLCHAIN.md` to what
the checks actually print.

**Why this exists.** `reports/PROOF.sha256` deliberately does not hash the three prose documents —
they can be edited without changing what the build or the audit compute — and until this script
existed nothing else looked at them either. So the documents could say "645 constants", "102
theorems", "21 files in the manifest", or publish a transcript of a gate run, and drift from the
truth without any step going red. A public verify page whose reader is invited to open a CI log
and compare it against these documents cannot rest on that.

**What is checked here.**

* **Published transcripts.** The `./scripts/check_axioms.sh` transcript and the
  `scripts/gen_proof_sha256.py --check` line quoted in `reports/PROOF.md` must be exactly what
  those commands print now, and the regression-fixture table published there must be exactly what
  `scripts/regression_fixtures.py --expected-table` renders. Those transcripts carry most of the
  numbers between them — constants scanned, files under the library, `.lean` files scanned,
  modules in the import closure, files in the manifest, fixture runs and their per-stage exit
  statuses — so checking them checks those numbers at their source rather than by regex.
* **Prose numbers.** The counts repeated in sentences (`645`, `102`, `10 files`, the fixture-run
  and failure-mode counts) must equal the values computed now, in every place they appear.
* **The pinned toolchain.** The version string, the release commit and the Linux archive digest
  quoted in the documents must match `.github/workflows/ci.yml` and `lean-toolchain`.
* **The fixture roster.** Every fixture `scripts/regression_fixtures.py` declares must have a row
  in the table in `reports/PROOF.md`, and that table must have no rows for fixtures that do not
  exist.
* **The published install script.** `reports/TOOLCHAIN.md` publishes a runnable script that
  nothing else in this repository executes — not CI, not the fixtures — and it drifted from the
  workflow once for exactly that reason. Two checks now hold it: there is exactly one `#!/bin/sh`
  block, inside the Install section, and it passes `sh -n`; and its `# CI step N [key].` labels
  cover the workflow's steps once each, in order, with each key occurring in that step's name.
  `.github/workflows/ci.yml` is the source of truth and is read structurally, not by regex over
  its text — see `parse_workflow_steps`, which is dependency-free and cross-checked against
  PyYAML wherever that happens to be installed.

**What is *not* checked here, and is not claimed to be.** Everything else in those documents —
the mathematical account, the I-D section references, the lemma tables, the boundary text, the
build timings and the `12 jobs` figure (illustrative, and machine-dependent by construction) — is
written and maintained by hand. This script makes the numbers and the transcripts honest. It does
not make the prose true, and `reports/PROOF.md`'s "Trust boundary" says so in those words.

Anti-vacuity: a claim whose pattern matches nothing is a failure, not a silent skip, and a run
with no claims registered fails outright. A checker that can pass while checking nothing is the
defect it exists to prevent.

Usage:
    check_doc_claims.py [--root DIR]     # exit 0 iff every registered claim holds
"""
import argparse
import difflib
import pathlib
import re
import shlex
import subprocess
import sys
import tempfile


# The SHA-256 of every Lean 4.31.0 release archive `reports/TOOLCHAIN.md` offers, recorded here so
# that the table in that document cannot drift on its own. Retrieved 2026-09-09 from GitHub's
# release API, re-derivable with:
#
#   curl -fsSL https://api.github.com/repos/leanprover/lean4/releases/tags/v4.31.0 \
#     | python3 -c 'import json,sys; [print(a["digest"], a["name"]) for a in json.load(sys.stdin)["assets"]]'
#
# Same-commit caveat as everything else here: these constants live in the repository they check.
# The linux entry is additionally required to equal the value .github/workflows/ci.yml installs,
# so the digest CI actually verifies and the digest the document offers cannot diverge.
LEAN_RELEASE_DIGESTS = {
    "lean-4.31.0-linux.tar.zst":
        "07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f",
    "lean-4.31.0-linux_aarch64.tar.zst":
        "b1bf1d3c586b76cf4a86212a595d8b9edd99f438a41cce85d5780fa9347c811b",
    "lean-4.31.0-darwin_aarch64.tar.zst":
        "264105500c8abdf37b68ffe03390a783ed259807807222698da8dd92d6ce0a27",
    "lean-4.31.0-darwin.tar.zst":
        "6dac7a8f9d6d0bc339b4ea9376c06a88f3fd1a7f462beb3c7ded9fbc934f3fb5",
}


# What this script is required to check, declared apart from the tables that implement it, in the
# same spirit as `DECLARED_RUNS` in scripts/regression_fixtures.py and the mandatory-file check in
# scripts/gen_proof_sha256.py. Emptying or shortening `transcripts` or `claims` below would
# otherwise be a green run over nothing — the recurring defect in this repository. This does not
# make the list tamper-proof (an edit here and there in one commit still passes; see "Trust
# boundary" in reports/PROOF.md), but it does mean a rule cannot fall out silently.
DECLARED_TRANSCRIPTS = (
    "the ./scripts/check_axioms.sh transcript",
    "the manifest --check line",
    "the regression-fixture table",
)
DECLARED_STRUCTURAL_CHECKS = (
    "the published install script is a single block and passes sh -n",
    "the published install script's CI step labels match .github/workflows/ci.yml",
    "the published install script selects the recorded archive for every recorded platform",
    "the commands inside each labelled block match the workflow step it mirrors",
)
DECLARED_CLAIM_LABELS = frozenset({
    "constant and theorem counts",
    "theorem count",
    "theorem count and the number of files they live in",
    "constant count",
    "fixture run and failure-mode counts",
    "the number of files in the hash manifest",
    "the Lean release commit",
    "the pinned Lean version",
    "the pinned release commit",
    "the pinned toolchain tag",
    "the version in the recorded toolchain self-report",
    "the lake job count",
})


INSTALL_HEADING = "## Install — the same procedure a human runs and CI runs"
WORKFLOW = ".github/workflows/ci.yml"
WORKFLOW_JOB = "lean"


# The only fields a step of this workflow may declare. See `parse_workflow_steps` for why the
# list is this short.
STEP_SCHEMA_KEYS = frozenset({"name", "run", "uses"})

# The same treatment for the two levels above a step, because the schema was closed at the wrong
# depth: `if: false` beside `runs-on:` disables the whole job, and every step-level check goes on
# reporting that the steps are exactly right. `strategy:`, `continue-on-error:`, `container:` and
# `services:` do their own versions of the same thing, and `on:` decides whether the workflow runs
# at all. Admitted keys, never a list of dangerous ones — a key GitHub adds tomorrow is refused
# before anyone has to decide what it means.
WORKFLOW_SCHEMA_KEYS = frozenset({"name", "on", "jobs"})
JOB_SCHEMA_KEYS = frozenset({"runs-on", "timeout-minutes", "env", "steps"})
DECLARED_JOBS = ("lean",)
DECLARED_TRIGGERS = frozenset({"push", "pull_request"})
# The runner image. Not pinned by digest and named in reports/PROOF.md as trusted unverified — the
# schema does not fix that and does not pretend to. What it does is make a change to it visible:
# swapping the image changes everything this repository says about reproducibility.
DECLARED_RUNNER = "ubuntu-latest"
# The job's environment. A `PATH` here would silently decide which `python3` and which `lean` run,
# so the set is exact rather than open.
DECLARED_JOB_ENV = frozenset({
    "EXPECTED_LEAN_VERSION", "EXPECTED_LEAN_COMMIT", "LEAN_ASSET", "LEAN_ASSET_SHA256",
})
USES_PIN_RE = re.compile(r"[\w.-]+/[\w.-]+@[0-9a-f]{40}")


class WorkflowParseError(Exception):
    """The workflow could not be read structurally. Fail closed; never guess."""


def parse_workflow_steps(text: str, job: str = WORKFLOW_JOB) -> list[dict]:
    """Every step of `job` as `{"name": ..., "run": ...}`, read structurally, without a YAML
    library.

    PyYAML is not in the standard library and this repository takes no dependencies, so this is a
    deliberately small reader for the shape `.github/workflows/ci.yml` actually has: block
    mappings, one block sequence of step mappings, double-quoted or plain scalars, and block
    scalars (`|`, `>`) whose contents are skipped by indentation. It is *not* a YAML parser and
    does not pretend to be: anything outside that shape raises `WorkflowParseError` rather than
    being silently reinterpreted. Where PyYAML happens to be installed, `parse_workflow_steps` is
    cross-checked against it (see `workflow_steps`), so this reader being wrong is itself
    caught on any machine that has the library — without ever requiring it.
    """
    lines = text.splitlines()

    def indent_of(i: int) -> int:
        return len(lines[i]) - len(lines[i].lstrip(" "))

    def is_skippable(i: int) -> bool:
        s = lines[i].strip()
        return not s or s.startswith("#")

    n = len(lines)

    def unquote(v: str) -> str:
        v = v.strip()
        if len(v) >= 2 and v[0] == v[-1] and v[0] in "\"'":
            return v[1:-1]
        return v

    def child_keys(start: int, parent_indent: int) -> tuple[dict[str, str], dict[str, bool]]:
        """Immediate `key: value` children of the block opened at `start`, and whether each has a
        body of its own (nested lines or a non-empty value)."""
        values: dict[str, str] = {}
        has_body: dict[str, bool] = {}
        child_indent = None
        last_key = None
        k = start + 1
        while k < n:
            if is_skippable(k):
                k += 1
                continue
            ind = indent_of(k)
            if ind <= parent_indent:
                break
            s = lines[k].strip()
            if child_indent is None:
                child_indent = ind
            if ind == child_indent:
                if ":" not in s:
                    raise WorkflowParseError(f"line {k + 1}: not a `key: value` line: {s!r}")
                key, _, value = s.partition(":")
                last_key = key.strip()
                values[last_key] = value.strip()
                has_body[last_key] = bool(value.strip())
            elif last_key is not None:
                has_body[last_key] = True
            k += 1
        return values, has_body

    # ---- the workflow's own top level ---------------------------------------------------------
    top_values: dict[str, str] = {}
    on_line = None
    jobs_line = None
    i = 0
    while i < n:
        if is_skippable(i) or indent_of(i) != 0:
            i += 1
            continue
        s = lines[i].strip()
        if ":" not in s:
            raise WorkflowParseError(f"line {i + 1}: not a `key: value` line at top level: {s!r}")
        key = s.partition(":")[0].strip()
        top_values[key] = s.partition(":")[2].strip()
        if key == "on":
            on_line = i
        if key == "jobs":
            jobs_line = i
        i += 1
    extra_top = set(top_values) - WORKFLOW_SCHEMA_KEYS
    if extra_top:
        raise WorkflowParseError(
            f"the workflow declares top-level key(s) {sorted(extra_top)}, which its schema does "
            f"not admit. Allowed: {sorted(WORKFLOW_SCHEMA_KEYS)}."
        )
    missing_top = WORKFLOW_SCHEMA_KEYS - set(top_values)
    if missing_top:
        raise WorkflowParseError(f"the workflow has no {sorted(missing_top)}")

    # `on:` decides whether any of this runs. The triggers are exact, and each must carry no
    # filter of its own: a `branches:` list under `push` is how a push to a branch with no open
    # pull request went unchecked once already.
    triggers, trigger_bodies = child_keys(on_line, 0)
    if set(triggers) != DECLARED_TRIGGERS:
        raise WorkflowParseError(
            f"the workflow triggers on {sorted(triggers)}, expected exactly "
            f"{sorted(DECLARED_TRIGGERS)}"
        )
    filtered = sorted(k for k, v in trigger_bodies.items() if v)
    if filtered:
        raise WorkflowParseError(
            f"trigger(s) {filtered} carry a filter; this workflow must run on every push (any "
            "branch) and every pull request, which is what README.md and reports/PROOF.md claim"
        )

    # ---- jobs -----------------------------------------------------------------------------
    job_names, _ = child_keys(jobs_line, 0)
    if tuple(sorted(job_names)) != tuple(sorted(DECLARED_JOBS)):
        raise WorkflowParseError(
            f"the workflow declares job(s) {sorted(job_names)}, expected exactly "
            f"{sorted(DECLARED_JOBS)}; an undeclared job runs whatever it likes"
        )

    i = jobs_line
    jobs_indent = 0
    i += 1

    job_indent = None
    while i < n:
        if is_skippable(i):
            i += 1
            continue
        ind = indent_of(i)
        if ind <= jobs_indent:
            raise WorkflowParseError(f"job `{job}` not found under `jobs:`")
        if job_indent is None:
            job_indent = ind
        if ind == job_indent and lines[i].strip() == f"{job}:":
            break
        i += 1
    else:
        raise WorkflowParseError(f"job `{job}` not found under `jobs:`")

    job_line = i
    job_values, _ = child_keys(job_line, job_indent)
    extra_job = set(job_values) - JOB_SCHEMA_KEYS
    if extra_job:
        raise WorkflowParseError(
            f"job `{job}` declares {sorted(extra_job)}, which its schema does not admit. "
            f"Allowed: {sorted(JOB_SCHEMA_KEYS)}. A key outside the schema may change whether or "
            "how the job runs — `if:`, `strategy:`, `continue-on-error:`, `container:` and "
            "`services:` all do — so it is refused until this checker knows what to make of it."
        )
    missing_job = JOB_SCHEMA_KEYS - set(job_values)
    if missing_job:
        raise WorkflowParseError(f"job `{job}` has no {sorted(missing_job)}")
    runner = unquote(job_values["runs-on"])
    if runner != DECLARED_RUNNER:
        raise WorkflowParseError(
            f"job `{job}` runs on {runner!r}, not the declared {DECLARED_RUNNER!r}. The image is "
            "not pinned by digest and is trusted unverified (see \"Trust boundary\" in "
            "reports/PROOF.md); changing it changes everything this repository says about "
            "reproducibility, so it may not change unnoticed."
        )
    env_line = next(
        (k for k in range(job_line + 1, n)
         if not is_skippable(k) and lines[k].strip() == "env:"), None)
    if env_line is None:
        raise WorkflowParseError(f"job `{job}` has no `env:` block")
    env_values, _ = child_keys(env_line, indent_of(env_line))
    if set(env_values) != DECLARED_JOB_ENV:
        raise WorkflowParseError(
            f"job `{job}` sets environment {sorted(env_values)}, expected exactly "
            f"{sorted(DECLARED_JOB_ENV)}; a variable here decides what the steps see, `PATH` "
            "above all"
        )

    i += 1
    steps_indent = None
    while i < n:
        if is_skippable(i):
            i += 1
            continue
        ind = indent_of(i)
        if ind <= job_indent:
            raise WorkflowParseError(f"job `{job}` has no `steps:`")
        if lines[i].strip() == "steps:":
            steps_indent = ind
            break
        i += 1
    if steps_indent is None:
        raise WorkflowParseError(f"job `{job}` has no `steps:`")

    def check_step_name(value: str, lineno: int) -> str:
        """Accept only a plain or simply-quoted scalar. Anything a real YAML parser would
        interpret differently from a literal reading is rejected, never guessed at.

        Each rejection below is a way this reader could have agreed with a label while GitHub
        Actions ran a step of a different name:
          * an alias (`*anchor`) or anchor (`&anchor`) reads here as the literal text `*anchor`,
            while YAML substitutes whatever the anchor holds;
          * a trailing `#` comment is not part of the value in YAML but is in a literal reading,
            so `name: real # claimed` would let the key `[claimed]` match a comment;
          * flow collections, tags and escapes have meanings a literal reading does not carry.
        """
        if value.startswith(("*", "&")):
            raise WorkflowParseError(
                f"line {lineno}: `name:` is a YAML anchor or alias ({value!r}); this reader will "
                "not resolve it and must not pretend the literal text is the step's name"
            )
        if value.startswith(("{", "[", "!", "?")):
            raise WorkflowParseError(
                f"line {lineno}: `name:` uses a YAML form this reader does not read ({value!r})"
            )
        if "\t" in value:
            raise WorkflowParseError(f"line {lineno}: tab in `name:`")
        if value[:1] in ("'", '"'):
            quote = value[0]
            if not value.endswith(quote) or len(value) < 2:
                raise WorkflowParseError(f"line {lineno}: unterminated quoted `name:` {value!r}")
            body = value[1:-1]
            if "\\" in body or quote in body:
                raise WorkflowParseError(
                    f"line {lineno}: quoted `name:` uses escaping this reader does not read"
                )
            return body
        if " #" in value or value.startswith("#"):
            raise WorkflowParseError(
                f"line {lineno}: `name:` appears to carry a trailing comment ({value!r}); YAML "
                "would drop it and this reader would not, so the two could disagree"
            )
        return value

    names: list[str] = []
    runs: list[str] = []
    uses: list[str] = []
    keys: list[set[str]] = []
    item_indent = None
    i += 1
    while i < n:
        if is_skippable(i):
            i += 1
            continue
        ind = indent_of(i)
        if ind <= steps_indent:
            break                                    # the sequence ended
        raw = lines[i]
        if "\t" in raw:
            raise WorkflowParseError(f"line {i + 1}: tab in a line inside `steps:`")
        stripped = raw.strip()
        if stripped in ("---", "..."):
            raise WorkflowParseError(f"line {i + 1}: document marker inside `steps:`")
        if stripped.startswith("- "):
            if item_indent is None:
                item_indent = ind
            elif ind != item_indent:
                raise WorkflowParseError(
                    f"line {i + 1}: step list item at indent {ind}, expected {item_indent}"
                )
            names.append(None)                       # placeholder for this step
            runs.append("")
            uses.append("")
            keys.append(set())
            stripped = stripped[2:].strip()
            key_indent = ind + 2
        elif item_indent is not None and ind == item_indent + 2:
            key_indent = ind
        else:
            # Deeper than a step's own keys, and not consumed by a block scalar or a nested
            # block below: this reader does not know what it is, so it stops. An earlier version
            # accepted any depth, which let a nested `with:`/`name:` be read as the step's name.
            raise WorkflowParseError(f"line {i + 1}: not understood inside `steps:`: {stripped!r}")

        if ":" not in stripped:
            raise WorkflowParseError(f"line {i + 1}: not a `key: value` line: {stripped!r}")

        key, _, value = stripped.partition(":")
        key, value = key.strip(), value.strip()
        if key == "<<" or value.startswith(("*", "&")):
            raise WorkflowParseError(
                f"line {i + 1}: YAML merge key or anchor/alias inside `steps:` ({stripped!r}); "
                "this reader resolves neither and will not guess"
            )
        if names:
            keys[-1].add(key)
        if value in ("|", ">", "|-", ">-", "|+", ">+") or value == "":
            # A block scalar, or a nested mapping/sequence (`with:`, `env:`). Either way its
            # contents are not this step's own fields. A `run:` block scalar is captured (its
            # commands are compared against the published script); anything else is skipped.
            body: list[str] = []
            i += 1
            while i < n and (is_skippable(i) or indent_of(i) > key_indent):
                if not is_skippable(i):
                    body.append(lines[i][key_indent:])
                i += 1
            if key == "run" and value != "":
                if not names:
                    raise WorkflowParseError("`run:` outside any step")
                runs[-1] = "\n".join(body)
            continue
        if key == "name":
            if not names:
                raise WorkflowParseError(f"line {i + 1}: `name:` outside any step")
            if names[-1] is not None:
                raise WorkflowParseError(f"line {i + 1}: step has more than one `name:`")
            names[-1] = check_step_name(value, i + 1)
        elif key == "run":
            if not names:
                raise WorkflowParseError(f"line {i + 1}: `run:` outside any step")
            runs[-1] = value
        elif key == "uses":
            if not names:
                raise WorkflowParseError(f"line {i + 1}: `uses:` outside any step")
            uses[-1] = value
        i += 1

    if not names:
        raise WorkflowParseError(f"job `{job}` declares no steps")
    unnamed = [k + 1 for k, v in enumerate(names) if v is None]
    if unnamed:
        raise WorkflowParseError(f"step(s) {unnamed} have no `name:`")

    # Strict schema. A step is `name` plus exactly one of `run` or a SHA-pinned `uses`, and
    # nothing else.
    #
    # This is the check that was missing, and its absence was the worst hole in the whole
    # construction: `if: false` on the regression-fixtures step, with the manifest regenerated as
    # any author would, produced a green run that never executed a single fixture. The label check
    # saw the step in place, the command comparison saw the same commands, and that the step would
    # not run was visible to nothing. `continue-on-error: true` does the same for the gate.
    # Rather than enumerate the fields that disable a step — a list that GitHub can extend without
    # telling us — the schema admits only the two fields this workflow uses and refuses everything
    # else, including fields that are perfectly ordinary elsewhere (`env`, `shell`,
    # `working-directory`, `id`, `with`, `timeout-minutes`). Adding one is then a deliberate act
    # that must come with a check for what it means.
    for idx, (name, seen) in enumerate(zip(names, keys), start=1):
        extra = seen - STEP_SCHEMA_KEYS
        if extra:
            raise WorkflowParseError(
                f"step {idx} ({name!r}) declares {sorted(extra)}, which this workflow's schema "
                f"does not admit. Allowed: {sorted(STEP_SCHEMA_KEYS)}. A field outside the schema "
                "may change whether or how the step runs — `if:` and `continue-on-error:` do "
                "exactly that — so it is refused until this checker knows what to make of it."
            )
        has_run, has_uses = "run" in seen, "uses" in seen
        if has_run == has_uses:
            raise WorkflowParseError(
                f"step {idx} ({name!r}) must have exactly one of `run:` or `uses:`, has "
                f"{'both' if has_run else 'neither'}"
            )
    for idx, (name, ref) in enumerate(zip(names, uses), start=1):
        if ref and not USES_PIN_RE.fullmatch(ref):
            raise WorkflowParseError(
                f"step {idx} ({name!r}) uses {ref!r}, which is not pinned by a 40-character "
                "commit SHA; a mutable tag can be repointed by the action's publisher"
            )
    return [{"name": nm, "run": rn, "uses": us} for nm, rn, us in zip(names, runs, uses)]


def workflow_steps(root: pathlib.Path) -> list[dict]:
    """`parse_workflow_steps`, cross-checked against PyYAML when it happens to be installed."""
    text = (root / WORKFLOW).read_text(encoding="utf-8")
    steps = parse_workflow_steps(text)
    try:
        import yaml  # noqa: PLC0415 — optional; never required
    except ImportError:
        return steps
    reference = yaml.safe_load(text)["jobs"][WORKFLOW_JOB]["steps"]
    ref_names = [s.get("name") for s in reference]
    if ref_names != [s["name"] for s in steps]:
        raise WorkflowParseError(
            "the dependency-free workflow reader disagrees with PyYAML about step names:\n"
            f"  reader: {[s['name'] for s in steps]}\n  PyYAML: {ref_names}"
        )
    ref_cmds = [commands_in(s.get("run") or "") for s in reference]
    own_cmds = [commands_in(s["run"]) for s in steps]
    if ref_cmds != own_cmds:
        raise WorkflowParseError(
            "the dependency-free workflow reader disagrees with PyYAML about step commands:\n"
            f"  reader: {own_cmds}\n  PyYAML: {ref_cmds}"
        )
    return steps


LABEL_RE = re.compile(r"^#\s*CI steps?\s+(\d+)(?:\s*-\s*(\d+))?\s*\[([^\]]*)\]\s*\.")

# The vocabulary of commands compared between a workflow step and the script block that mirrors
# it. This is **not** shell equivalence and is not offered as such: it is the set of tool
# invocations that decide what a step actually does here, and everything outside it (`echo`,
# `mkdir`, `mv`, `case`, variable assignments, redirections) is ignored. Comparing free shell text
# would be either brittle or meaningless; comparing this vocabulary caught a real divergence —
# `lake --version` present in CI's self-report step and absent from the published script — that
# label-only comparison could not see.
# ---------------------------------------------------------------------------------------------
# Command comparison between a workflow step and the script block that mirrors it.
#
# The rule is inverted, the way the coverage rule was inverted: **every** command in command
# position is compared, and only what is declared below as indifferent is dropped. The previous
# version compared a vocabulary of commands it recognised, which meant anything it did not
# recognise was silently equal — so `node evil.js` or `python3 -c '...'`, appended to the `run:` of
# a step that already existed, changed no compared set and passed. A new *step* was caught by the
# label check and a new *file* by the coverage rule; a new command inside an old step was caught
# by nothing.
#
# The price is real and accepted: `echo`, `mkdir` and friends now have to be named. Naming them is
# the point — an explicit list of what is considered indifferent can be read and argued with,
# where "everything unfamiliar is fine" cannot.

# Shell syntax, not commands. Words that open or close a construct.
SHELL_KEYWORDS = frozenset({
    "if", "then", "elif", "else", "fi", "for", "while", "until", "do", "done",
    "case", "esac", "in", "function", "select", ";;", "{", "}", "!",
})

# Declared indifferent: shell builtins and utilities that neither execute anything from this
# repository nor fetch anything from outside it. Each is here because its presence or absence
# cannot change what a step verifies. `eval`, `sh`, `bash`, `python3`, `node` and anything else
# that can run code are deliberately **not** on this list.
# Kept to what actually occurs: an entry that never fires is a place something could hide later,
# so the checker reports unused entries and this list is pruned to match rather than padded
# against hypothetical future need. Adding a command here is a deliberate, reviewable act.
IGNORED_COMMANDS = frozenset({
    # shell builtins that change no file and run nothing from this repository
    "set", "echo", "cd", "export", "exit", "[",
    # file and path utilities whose presence cannot change what a step verifies
    "mkdir", "rm", "mv", "dirname", "mktemp", "tr",
    # an inert query about the host
    "uname",
})

# Prefixes that stand in front of a command without being one.
COMMAND_PREFIXES = frozenset({"time", "exec", "nohup", "env"})

# Commands that may never be declared indifferent, whatever else changes.
#
# An earlier attempt guarded the ignore list by requiring it to be disjoint from what is compared
# — which cannot fire, because anything named in the ignore list is by construction absent from
# the compared set. This is the check that can: moving `curl`, `node` or `eval` into
# IGNORED_COMMANDS fails outright. It is a **denylist and therefore not complete** — an
# interpreter nobody thought of could still be declared indifferent — but it names the ways code
# and network reach actually enter a step here, and it turns the most likely mistake into a red
# run instead of a quiet one.
NEVER_IGNORABLE = frozenset({
    "eval", "source", ".", "sh", "bash", "zsh", "dash", "ksh",
    "python", "python3", "node", "ruby", "perl", "php", "deno", "bun",
    "curl", "wget", "nc", "ncat", "ssh", "scp", "rsync", "git",
    "lake", "lean", "elan", "make", "cmake", "docker", "npm", "npx", "pip", "pip3",
    "sha256sum", "shasum", "tar", "unzip", "find", "xargs",
})

# Declared spelling equivalences: two commands that do the same job under different names on
# different systems, normalised so that a legitimate portability branch is not read as a
# divergence. `shasum -a 256 -c` is macOS's spelling of GNU `sha256sum -c`; the install script
# offers both because a reader may be on either, while CI is always Linux.
COMMAND_NORMALISATIONS = (
    (re.compile(r"^(?:sha256sum|shasum)\b(?=.*\s-c\b)"), "sha256sum -c"),
)

_ASSIGNMENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")
_FLAG = re.compile(r"^--?[A-Za-z0-9][\w-]*$")
_SCRIPT_PATH = re.compile(r"^\.?/?scripts/[\w./-]+$")
_BARE_WORD = re.compile(r"^[a-z][a-z0-9._-]*$")
_CASE_OPEN = re.compile(r"^case\b.*\bin$")
_CASE_PATTERN = re.compile(r"^[^;]*\)\s*(?:;;)?$")


SUBSTITUTION_PLACEHOLDER = "SUBST"


def _extract_substitutions(line: str) -> tuple[str, list[str], list[str]]:
    """Replace each `$( … )` / backtick substitution with a placeholder word.

    Returns (line with placeholders, substitution bodies, problems). Cutting the line at `$(`
    instead — which is what an earlier version did — left the outer piece with an unbalanced
    quote, since the closing `"` sits after the substitution: `mkdir -p "$(dirname X)"` became
    `mkdir -p "`. A placeholder keeps both halves quotable, and the body is returned to be scanned
    in its own right, because a substitution is a command position.
    """
    out: list[str] = []
    bodies: list[str] = []
    problems: list[str] = []
    i, n = 0, len(line)
    sq = dq = False
    while i < n:
        c = line[i]
        if sq:
            out.append(c)
            sq = c != "'"
            i += 1
            continue
        if c == "'" and not dq:
            sq = True
            out.append(c)
            i += 1
            continue
        if c == '"':
            dq = not dq
            out.append(c)
            i += 1
            continue
        opener = "$(" if line.startswith("$(", i) else ("`" if c == "`" else None)
        if opener is None:
            out.append(c)
            i += 1
            continue
        j = i + len(opener)
        depth = 1
        b_sq = b_dq = False
        while j < n:
            d = line[j]
            if b_sq:
                b_sq = d != "'"
            elif d == "'" and not b_dq:
                b_sq = True
            elif d == '"':
                b_dq = not b_dq
            elif not b_dq:
                if opener == "$(" and line.startswith("$(", j):
                    depth += 1
                    j += 1
                elif opener == "$(" and d == ")":
                    depth -= 1
                    if depth == 0:
                        break
                elif opener == "`" and d == "`":
                    depth = 0
                    break
            j += 1
        if j >= n:
            problems.append(f"unterminated command substitution in {line.strip()!r}")
            out.append(c)
            i += 1
            continue
        bodies.append(line[i + len(opener):j])
        out.append(SUBSTITUTION_PLACEHOLDER)
        i = j + 1
    if sq or dq:
        problems.append(f"unbalanced quote in {line.strip()!r}")
    return "".join(out), bodies, problems


def _command_positions(line: str) -> tuple[list[str], list[str]]:
    """Split a shell line into the pieces that begin at a command position.

    Substitutions are lifted out first (see above) and returned as pieces of their own, since a
    substitution body runs. What remains is split on `;`, `|`, `&`, `&&`, `||` and `(` outside
    quotes; a redirection such as `2>&1` is text, not a separator; a trailing `#` comment ends the
    line.
    """
    flat, bodies, problems = _extract_substitutions(line)
    pieces: list[str] = []
    cur: list[str] = []
    sq = dq = False
    i, n = 0, len(flat)
    while i < n:
        c = flat[i]
        if sq:
            cur.append(c)
            sq = c != "'"
            i += 1
            continue
        if c == "'" and not dq:
            sq = True
            cur.append(c)
            i += 1
            continue
        if c == '"':
            dq = not dq
            cur.append(c)
            i += 1
            continue
        if not dq:
            if c == "#" and (not cur or cur[-1].isspace()):
                break
            if c == "&" and ((cur and cur[-1] == ">") or flat.startswith("&>", i)):
                cur.append(c)
                i += 1
                continue
            if flat.startswith("&&", i) or flat.startswith("||", i):
                pieces.append("".join(cur))
                cur = []
                i += 2
                continue
            if c in "|;&(":
                pieces.append("".join(cur))
                cur = []
                i += 1
                continue
            if c == ")":
                pieces.append("".join(cur))
                cur = []
                i += 1
                continue
        cur.append(c)
        i += 1
    pieces.append("".join(cur))
    for body in bodies:
        sub_pieces, sub_problems = _command_positions(body)
        pieces += sub_pieces
        problems += sub_problems
    return pieces, problems


# Constructs this recogniser does not read. Finding one is an **error**, not an empty result.
#
# That inversion is the point of this round. The scanner used to return nothing for a line it did
# not understand, which meant `CI_X=1 node evil.js`, `command node evil.js`,
# `trap 'node evil.js' EXIT` and `if node evil.js; then` were each compared as no commands at all
# — unknown treated as safe. The four forms are handled below; everything still unhandled now
# fails loudly, so the set of shell this comparison covers is a fact about the code rather than a
# hope. These scripts are ours and are about a hundred lines; when one needs a construct from this
# list, the honest move is to add support for it deliberately, not to let it pass unread.
UNSUPPORTED_MARKERS = (
    ("<<", "here-document"),
    ("<(", "process substitution"),
    (">(", "process substitution"),
    ("$((", "arithmetic substitution"),
    (";&", "case fallthrough"),
    ("${!", "indirect parameter expansion"),
)

# Keywords whose remainder is itself a command and must be scanned, not skipped.
RECURSING_KEYWORDS = frozenset({"if", "elif", "while", "until", "!"})


def _scan_words(words: list[str], compared: set[str], ignored_seen: set[str],
                unsupported: set[str], depth: int = 0) -> None:
    """Classify one command position, following the constructs listed in the module docstring."""
    if depth > 4:
        unsupported.add("command nesting deeper than this recogniser follows")
        return
    while words and words[0] in COMMAND_PREFIXES:
        words = words[1:]
    while words and _ASSIGNMENT.match(words[0]):
        words = words[1:]          # `NAME=value cmd …` — the command is what follows
    if not words:
        return
    head = words[0]
    if head.endswith(")"):
        return                     # a `case` pattern
    if head in RECURSING_KEYWORDS:
        _scan_words(words[1:], compared, ignored_seen, unsupported, depth + 1)
        return
    if head in SHELL_KEYWORDS:
        return
    if head.startswith(("$", "`", "{")):
        unsupported.add(f"indirect or grouped command {head!r}")
        return
    if head == "trap":
        # The payload is shell, and it runs. `trap 'node evil.js' EXIT` used to scan as nothing.
        payload_pieces, payload_problems = _command_positions(
            words[1] if len(words) > 1 else "")
        unsupported.update(payload_problems)
        for piece in payload_pieces:
            _scan_piece(piece, compared, ignored_seen, unsupported, depth + 1)
        return
    if head in ("command", "env"):
        rest = words[1:]
        if head == "command" and rest and rest[0] in ("-v", "-V", "-p"):
            return                 # a lookup: resolves a name, runs nothing
        _scan_words(rest, compared, ignored_seen, unsupported, depth + 1)
        return
    if head in IGNORED_COMMANDS:
        ignored_seen.add(head)
        return
    joined = " ".join(words)
    for pattern, replacement in COMMAND_NORMALISATIONS:
        if pattern.search(joined):
            compared.add(replacement)
            return
    arg = words[1] if len(words) > 1 else ""
    if _FLAG.match(arg) or _SCRIPT_PATH.match(arg) or _BARE_WORD.match(arg):
        compared.add(f"{head} {arg}")
    else:
        compared.add(head)


def _scan_piece(piece: str, compared: set[str], ignored_seen: set[str],
                unsupported: set[str], depth: int = 0) -> None:
    try:
        words = shlex.split(piece, posix=True)
    except ValueError as e:
        unsupported.add(f"unparsable shell ({e}): {piece.strip()!r}")
        return
    _scan_words(words, compared, ignored_seen, unsupported, depth)


def command_scan(text: str) -> tuple[set[str], set[str], set[str]]:
    """Return (commands compared, ignored commands seen, unsupported constructs found).

    Command position means: the start of a line, or immediately after `|`, `;`, `&`, `(`, `$(` or
    a backtick, optionally behind one of COMMAND_PREFIXES and any number of `NAME=value`
    assignments. Full-line and trailing comments are dropped, backslash continuations joined, and
    `case` patterns recognised as syntax.
    """
    compared: set[str] = set()
    ignored_seen: set[str] = set()
    unsupported: set[str] = set()
    in_case = False
    joined_lines: list[str] = []
    for raw in text.splitlines():
        if joined_lines and joined_lines[-1].endswith("\\"):
            joined_lines[-1] = joined_lines[-1][:-1].rstrip() + " " + raw.strip()
        else:
            joined_lines.append(raw)
    for raw in joined_lines:
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        for marker, what in UNSUPPORTED_MARKERS:
            if marker in line:
                unsupported.add(f"{what} in {line!r}")
        if _CASE_OPEN.match(line):
            in_case = True
        elif line == "esac":
            in_case = False
        if in_case and _CASE_PATTERN.match(line) and not line.startswith("case"):
            continue
        pieces, piece_problems = _command_positions(line)
        unsupported.update(piece_problems)
        for piece in pieces:
            _scan_piece(piece, compared, ignored_seen, unsupported)
    return compared, ignored_seen, unsupported


def commands_in(text: str) -> list[str]:
    """The compared commands of a chunk of shell, sorted."""
    return sorted(command_scan(text)[0])


def extract_install_script(doc: str, problems: list[str]) -> str | None:
    """The one `#!/bin/sh` block published in the Install section, or None with a problem filed.

    Same uniqueness rule as the transcripts: exactly one such block in the whole document, inside
    the section that is supposed to hold it. A second copy is how a stale script sits beside a
    correct one, and no block at all is how the section quietly stops publishing a procedure while
    the prose goes on describing it.
    """
    hits = [(off, body) for off, body in fenced_blocks(doc)
            if body.lstrip().startswith("#!/bin/sh")]
    if len(hits) != 1:
        problems.append(
            f"reports/TOOLCHAIN.md: expected exactly one `#!/bin/sh` block (the install script), "
            f"found {len(hits)} — a procedure that is missing, or published twice, cannot be the "
            "one this document claims CI matches"
        )
        return None
    off, body = hits[0]
    span = section_span(doc, INSTALL_HEADING)
    if span is None:
        problems.append(f"reports/TOOLCHAIN.md: section {INSTALL_HEADING!r} is gone")
    elif not (span[0] <= off < span[1]):
        problems.append(
            f"reports/TOOLCHAIN.md: the install script is published outside {INSTALL_HEADING!r}"
        )
    return body


def check_install_script_syntax(script: str, problems: list[str]) -> None:
    """`sh -n` the published script.

    **What this does not establish.** `sh -n` parses; it does not run. It catches a block that
    stopped being a valid shell script — an unbalanced quote, a broken `case`, a mangled
    here-doc — and nothing at all about whether the script installs the right toolchain or runs
    the right checks. That the *steps* are the right ones, in the right order, is the separate
    label check below; that they do what they say remains unverified, because nothing here
    downloads 500 MB of toolchain to find out.
    """
    with tempfile.NamedTemporaryFile("w", suffix=".sh", delete=False) as fh:
        fh.write(script)
        path = fh.name
    try:
        proc = subprocess.run(["sh", "-n", path], capture_output=True, text=True)
        if proc.returncode != 0:
            problems.append(
                "reports/TOOLCHAIN.md: the published install script is not valid shell "
                f"(`sh -n` exited {proc.returncode}):\n{(proc.stdout + proc.stderr).strip()}"
            )
    finally:
        pathlib.Path(path).unlink(missing_ok=True)


def check_install_script_labels(script: str, ci_steps: list[dict], problems: list[str]) -> None:
    """The script's `# CI step N [key].` labels against the workflow's actual step sequence.

    Each block of the script is labelled with the CI step it corresponds to and a key that must
    occur in that step's `name`. The labels, expanded, must cover step 1 to step N exactly once
    each, in order. That is what catches the failure this check exists for: a step added to,
    removed from, or reordered within the workflow while the published script stays as it was.

    **What this does not establish.** It compares *positions and names*, not behaviour: a label
    can point at the right step while the shell under it does something else entirely. Equivalence
    of what each step does is not machine-checked and is not claimed to be.
    """
    labels: list[tuple[int, int, list[str]]] = []
    blocks: list[list[str]] = []
    for line in script.splitlines():
        m = LABEL_RE.match(line.strip())
        if m:
            lo = int(m.group(1))
            hi = int(m.group(2)) if m.group(2) else lo
            keys = [k.strip() for k in m.group(3).split("|")]
            labels.append((lo, hi, keys))
            blocks.append([])
        elif blocks:
            blocks[-1].append(line)

    if not labels:
        problems.append(
            "reports/TOOLCHAIN.md: the install script carries no `# CI step N [key].` labels, so "
            "its correspondence to the workflow cannot be checked at all"
        )
        return

    covered: list[int] = []
    keyed: dict[int, str] = {}
    for lo, hi, keys in labels:
        span = list(range(lo, hi + 1))
        if len(keys) != len(span):
            problems.append(
                f"reports/TOOLCHAIN.md: label `CI step{'s' if hi > lo else ''} {lo}"
                f"{f'-{hi}' if hi > lo else ''}` covers {len(span)} step(s) but names "
                f"{len(keys)} key(s): {keys}"
            )
            return
        covered += span
        keyed.update(dict(zip(span, keys)))

    expected = list(range(1, len(ci_steps) + 1))
    if covered != expected:
        problems.append(
            "reports/TOOLCHAIN.md: the install script's CI step labels do not cover the "
            f"workflow's steps exactly once, in order.\n"
            f"      workflow has {len(ci_steps)} step(s): {expected}\n"
            f"      script labels cover:            {covered}"
        )

    # Commands, not just labels. A label can point at the right step while the block under it
    # runs something else — which is how `lake --version`, present in CI's self-report step, was
    # missing from the published script without anything noticing.
    for (lo, hi, _), body in zip(labels, blocks):
        in_ci = sorted({
            c for number in range(lo, hi + 1)
            if 1 <= number <= len(ci_steps)
            for c in commands_in(ci_steps[number - 1]["run"])
        })
        in_script = commands_in("\n".join(body))
        if in_ci != in_script:
            span = f"{lo}" if hi == lo else f"{lo}-{hi}"
            problems.append(
                f"reports/TOOLCHAIN.md: the commands under `CI step{'s' if hi > lo else ''} "
                f"{span}` differ from the workflow's.\n"
                f"      workflow runs: {in_ci}\n"
                f"      script runs:   {in_script}\n"
                f"      only in workflow: {sorted(set(in_ci) - set(in_script))}\n"
                f"      only in script:   {sorted(set(in_script) - set(in_ci))}"
            )

    # Anti-vacuity for the comparison itself. Under the inverted rule the danger is no longer a
    # vocabulary that recognises nothing but an ignore list that swallows everything.
    all_ci_commands: set[str] = set()
    all_ignored_seen: set[str] = set()
    all_unsupported: set[str] = set()
    for s in ci_steps:
        seen_cmds, seen_ignored, seen_unsupported = command_scan(s["run"])
        all_ci_commands |= seen_cmds
        all_ignored_seen |= seen_ignored
        all_unsupported |= {f"{WORKFLOW} step {s['name']!r}: {u}" for u in seen_unsupported}
    script_cmds, script_ignored, script_unsupported = command_scan(script)
    all_ignored_seen |= script_ignored
    all_unsupported |= {f"the published install script: {u}" for u in script_unsupported}

    if all_unsupported:
        problems.append(
            "shell this comparison does not read, which must be an error rather than an empty "
            "result — an unread line contributes no commands and would compare as equal:\n      "
            + "\n      ".join(sorted(all_unsupported))
        )

    if not IGNORED_COMMANDS:
        problems.append("IGNORED_COMMANDS is empty — a declared list that names nothing")
    if not all_ci_commands:
        problems.append(
            f"no command at all was recognised in {WORKFLOW} — either the workflow runs nothing "
            "or the scanner has stopped seeing commands, and either way comparing empty sets "
            "would pass"
        )
    forbidden_ignores = sorted(IGNORED_COMMANDS & NEVER_IGNORABLE)
    if forbidden_ignores:
        problems.append(
            f"command(s) {forbidden_ignores} are declared indifferent but appear in "
            "NEVER_IGNORABLE: each of them runs code or reaches the network, so dropping it from "
            "the comparison would hide exactly what the comparison is for"
        )
    unused_ignores = sorted(IGNORED_COMMANDS - all_ignored_seen)
    if unused_ignores:
        print(
            "check_doc_claims.py: note — declared indifferent but never seen: "
            + ", ".join(unused_ignores)
            + ". Each is a command this comparison would drop if it appeared; none of them "
            "appears today. Prune what is not needed rather than letting the list grow into a "
            "place things can hide.",
            file=sys.stderr,
        )

    rows, mismatched = [], False
    for number in expected:
        name = ci_steps[number - 1]["name"]
        key = keyed.get(number)
        ok = key is not None and key.lower() in name.lower()
        mismatched = mismatched or not ok
        rows.append(f"      {'ok ' if ok else 'BAD'} {number:>2}  ci.yml: {name}\n"
                    f"               script: [{key}]")
    if mismatched:
        problems.append(
            "reports/TOOLCHAIN.md: a label's key does not occur in the name of the workflow step "
            "it claims to mirror — the workflow's steps and the published script have diverged:\n"
            + "\n".join(rows)
        )


SELECTION_RE = re.compile(
    r"^# --- platform selection.*?^# --- end platform selection[^\n]*$",
    re.S | re.M,
)

# The complete branch set the published script may have: `(uname -s, uname -m)` -> archive.
# `Linux/arm64` is a declared alias — some Linux ARM systems report `arm64` where others report
# `aarch64` — and it is written down here rather than tolerated, because tolerating unlisted
# branches is what let the previous version of this check pass a script that quietly handed
# FreeBSD a Linux build. The comparison below is **exact equality**: a branch for a platform not
# in this table fails, even when every required branch and the `*)` default are present and the
# set of archives offered is unchanged.
DECLARED_PLATFORM_BRANCHES = {
    ("Linux", "x86_64"): "lean-4.31.0-linux.tar.zst",
    ("Linux", "aarch64"): "lean-4.31.0-linux_aarch64.tar.zst",
    ("Linux", "arm64"): "lean-4.31.0-linux_aarch64.tar.zst",
    ("Darwin", "arm64"): "lean-4.31.0-darwin_aarch64.tar.zst",
    ("Darwin", "x86_64"): "lean-4.31.0-darwin.tar.zst",
}
CI_PLATFORM = ("Linux", "x86_64")


class PlatformParseError(Exception):
    """The platform-selection block is not in the one form this checker reads."""


def parse_platform_cases(fragment: str) -> dict[tuple[str, str], tuple[str, str]]:
    """Read `case "$(uname -s)/$(uname -m)" in … esac` structurally. Never execute it.

    An earlier version of this check *ran* the fragment with a stubbed `uname`. That answered the
    question but overstated its own safety: it executed text taken from a Markdown file, in the
    working directory, with only `uname` shadowed — absolute paths, network calls and writes to
    the tree were all still available to it, and there was no timeout. Since the accepted form is
    known and small, parsing it is both stricter and free of that: anything outside the form
    raises rather than being run to find out what it does.

    Accepted, and nothing else: one `case` on `"$(uname -s)/$(uname -m)"`; branches whose patterns
    are `System/Machine` (several separated by `|`); each non-default branch assigning exactly one
    `ASSET` and one `DIGEST` and nothing else; and a final `*)` branch that assigns neither and
    exits nonzero.
    """
    lines = [ln.rstrip() for ln in fragment.splitlines()]
    body = [ln for ln in lines if ln.strip() and not ln.strip().startswith("#")]
    if not body or body[0].strip() != 'case "$(uname -s)/$(uname -m)" in':
        raise PlatformParseError(
            "the block does not open with `case \"$(uname -s)/$(uname -m)\" in`"
        )
    if body[-1].strip() != "esac":
        raise PlatformParseError("the block does not close with `esac`")

    cases: dict[tuple[str, str], tuple[str, str]] = {}
    default_seen = False
    i, n = 1, len(body) - 1
    while i < n:
        head = body[i].strip()
        if not head.endswith(")"):
            raise PlatformParseError(f"expected a branch pattern ending in `)`, got {head!r}")
        patterns = [pat.strip() for pat in head[:-1].split("|")]
        i += 1
        branch: list[str] = []
        while i < n and body[i].strip() != ";;":
            branch.append(body[i].strip())
            i += 1
        if i >= n:
            raise PlatformParseError(f"branch {head!r} is not terminated by `;;`")
        i += 1                                        # step over the `;;`

        assets = [ln.split("=", 1)[1] for ln in branch if ln.startswith("ASSET=")]
        digests = [ln.split("=", 1)[1] for ln in branch if ln.startswith("DIGEST=")]
        if patterns == ["*"]:
            default_seen = True
            if assets or digests:
                raise PlatformParseError(
                    "the default branch assigns an archive; an unrecognised platform must be "
                    "refused, not given some other platform's build"
                )
            if not any(re.fullmatch(r"exit\s+[1-9]\d*", ln) for ln in branch):
                raise PlatformParseError("the default branch does not exit nonzero")
            continue
        if len(assets) != 1 or len(digests) != 1:
            raise PlatformParseError(
                f"branch {head!r} must assign exactly one ASSET and one DIGEST, got "
                f"{len(assets)} and {len(digests)}"
            )
        stray = [ln for ln in branch
                 if not ln.startswith(("ASSET=", "DIGEST="))]
        if stray:
            raise PlatformParseError(f"branch {head!r} contains lines this reader does not "
                                     f"accept: {stray}")
        for pat in patterns:
            if not re.fullmatch(r"[A-Za-z0-9_]+/[A-Za-z0-9_]+", pat):
                raise PlatformParseError(f"branch pattern {pat!r} is not `System/Machine`")
            sysname, machine = pat.split("/")
            if (sysname, machine) in cases:
                raise PlatformParseError(f"platform {pat} is matched by two branches")
            cases[(sysname, machine)] = (assets[0], digests[0])
    if not default_seen:
        raise PlatformParseError("no `*)` branch: an unrecorded platform would fall through")
    if not cases:
        raise PlatformParseError("no platform branches at all")
    return cases


def check_install_script_platforms(script: str, ci_asset: str | None, ci_digest: str | None,
                                   problems: list[str]) -> None:
    """The published script must select each recorded platform's archive and digest.

    A constant is exactly what went wrong here: the script once hard-wired one platform's pair, so
    a reader on Linux — the platform CI itself runs on — would have downloaded and unpacked a
    macOS build while this document called the procedure equivalent to CI's.
    """
    m = SELECTION_RE.search(script)
    if not m:
        problems.append(
            "reports/TOOLCHAIN.md: the install script has no `# --- platform selection` block, "
            "so which archive it picks on which platform cannot be established"
        )
        return
    try:
        cases = parse_platform_cases(m.group(0))
    except PlatformParseError as e:
        problems.append(f"reports/TOOLCHAIN.md: the platform-selection block is not readable: {e}")
        return

    # Exact equality of the branch set, not "the required ones are present". An extra branch is
    # a platform that has silently stopped being refused, whatever else is in place.
    extra = sorted(set(cases) - set(DECLARED_PLATFORM_BRANCHES))
    missing = sorted(set(DECLARED_PLATFORM_BRANCHES) - set(cases))
    if extra:
        problems.append(
            "reports/TOOLCHAIN.md: the install script has branch(es) for platform(s) this "
            f"repository does not declare: {['/'.join(k) for k in extra]}. Those platforms are no "
            "longer refused — they now receive some other platform's build. Declare them in "
            "DECLARED_PLATFORM_BRANCHES with their own archive, or remove the branch."
        )
    if missing:
        problems.append(
            "reports/TOOLCHAIN.md: the install script has no branch for declared platform(s) "
            f"{['/'.join(k) for k in missing]}"
        )
    for key, expected_asset in DECLARED_PLATFORM_BRANCHES.items():
        chosen = cases.get(key)
        if chosen is None:
            continue
        asset, digest = chosen
        if asset != expected_asset:
            problems.append(
                f"reports/TOOLCHAIN.md: on {key[0]}/{key[1]} the install script selects {asset}, "
                f"expected {expected_asset}"
            )
        elif LEAN_RELEASE_DIGESTS.get(asset) != digest:
            problems.append(
                f"reports/TOOLCHAIN.md: on {key[0]}/{key[1]} the install script pairs {asset} "
                f"with digest {digest}, the recorded digest is {LEAN_RELEASE_DIGESTS.get(asset)}"
            )

    covered = {asset for asset, _ in cases.values()}
    if covered != set(LEAN_RELEASE_DIGESTS):
        problems.append(
            "reports/TOOLCHAIN.md: the install script does not offer every recorded archive; "
            f"offers {sorted(covered)}, recorded {sorted(LEAN_RELEASE_DIGESTS)}"
        )
    runner = cases.get(CI_PLATFORM)
    if runner is not None and ci_asset is not None and runner[0] != ci_asset:
        problems.append(
            f"reports/TOOLCHAIN.md: on the runner's platform ({CI_PLATFORM[0]}/{CI_PLATFORM[1]}) "
            f"the install script selects {runner[0]}, but {WORKFLOW} installs {ci_asset} — the "
            "local procedure and CI would install different builds"
        )
    if runner is not None and ci_digest is not None and runner[1] != ci_digest:
        problems.append(
            f"reports/TOOLCHAIN.md: on the runner's platform the install script verifies digest "
            f"{runner[1]}, but {WORKFLOW} verifies {ci_digest}"
        )


def run(cmd: list[str], cwd: pathlib.Path) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def extract(pattern: str, text: str, label: str, problems: list[str]) -> str | None:
    m = re.search(pattern, text)
    if not m:
        problems.append(f"could not read {label} out of the command output — pattern {pattern!r}")
        return None
    return m.group(1)


def fenced_blocks(text: str) -> list[tuple[int, str]]:
    """Every fenced code block in `text`, as (offset of the block's first line, content)."""
    return [(m.start(1), m.group(1)) for m in re.finditer(r"```[a-z]*\n(.*?)```", text, flags=re.S)]


def section_span(text: str, heading: str) -> tuple[int, int] | None:
    """The half-open span of the section introduced by `heading`, up to the next heading."""
    m = re.search(rf"^{re.escape(heading)}\s*$", text, flags=re.M)
    if not m:
        return None
    nxt = re.search(r"^#{1,6} ", text[m.end():], flags=re.M)
    return (m.end(), m.end() + nxt.start() if nxt else len(text))


def check_transcript(doc: str, doc_name: str, heading: str, expected: str,
                     label: str, problems: list[str]) -> None:
    """Require exactly one block whose first line matches, inside the named section, equal to
    `expected`.

    Substring containment is not enough and was the previous bug: a document could keep one
    correct block and grow a second, stale or contradictory one beside it, and still pass. So:
    the block is located by its first line, there must be exactly one such block *in the whole
    document*, it must sit inside the section that is supposed to hold it, and it must be equal
    to what the command prints — not merely contain it.
    """
    marker = expected.splitlines()[0].rstrip()
    hits = [(off, body) for off, body in fenced_blocks(doc)
            if body.splitlines() and body.splitlines()[0].rstrip() == marker]
    if not hits:
        problems.append(
            f"{doc_name}: no fenced block starts with {marker!r} — {label} is not published at "
            "all, so nothing was compared"
        )
        return
    if len(hits) > 1:
        problems.append(
            f"{doc_name}: {len(hits)} fenced blocks start with {marker!r}. Exactly one copy of "
            f"{label} may be published; otherwise a stale copy can sit beside a correct one and "
            "this check would still pass"
        )
        return
    off, body = hits[0]
    span = section_span(doc, heading)
    if span is None:
        problems.append(f"{doc_name}: section {heading!r}, which must hold {label}, is gone")
    elif not (span[0] <= off < span[1]):
        problems.append(
            f"{doc_name}: {label} is published outside the section {heading!r} it belongs to"
        )
    if body.rstrip("\n") != expected.rstrip("\n"):
        problems.append(
            f"{doc_name}: {label} is not what the command prints now.\n"
            + "\n".join(
                difflib.unified_diff(
                    body.rstrip("\n").splitlines(),
                    expected.rstrip("\n").splitlines(),
                    lineterm="",
                    fromfile="published in the document",
                    tofile="printed by the command now",
                )
            )
        )


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".", help="repository root (default: cwd)")
    args = ap.parse_args()
    root = pathlib.Path(args.root).resolve()
    sys.path.insert(0, str(root / "scripts"))

    problems: list[str] = []
    docs = {}
    for name in ("README.md", "reports/PROOF.md", "reports/TOOLCHAIN.md"):
        path = root / name
        if not path.is_file():
            print(f"FAIL: {name} does not exist under {root}", file=sys.stderr)
            return 1
        docs[name] = path.read_text(encoding="utf-8")

    # ---------------------------------------------------------------- structural checks --------
    # First, because it needs nothing else and because a missing or broken script should say so
    # rather than surfacing as some later check's confusion. This is the artefact nothing in this
    # repository executes — not CI, not the fixtures — which is exactly why it drifted once while
    # its description said otherwise.
    try:
        ci_steps = workflow_steps(root)
    except WorkflowParseError as e:
        print(f"check_doc_claims.py: FAIL — could not read {WORKFLOW} structurally: {e}",
              file=sys.stderr)
        return 1

    ci_text = (root / WORKFLOW).read_text(encoding="utf-8")
    ci_asset_m = re.search(r'LEAN_ASSET:\s*"([^"]+)"', ci_text)
    ci_digest_m = re.search(r'LEAN_ASSET_SHA256:\s*"([^"]+)"', ci_text)

    structural_run: list[str] = []
    install_script = extract_install_script(docs["reports/TOOLCHAIN.md"], problems)
    structural_run.append(DECLARED_STRUCTURAL_CHECKS[0])
    if install_script is not None:
        check_install_script_syntax(install_script, problems)
        check_install_script_labels(install_script, ci_steps, problems)
        structural_run.append(DECLARED_STRUCTURAL_CHECKS[1])
        check_install_script_platforms(
            install_script,
            ci_asset_m.group(1) if ci_asset_m else None,
            ci_digest_m.group(1) if ci_digest_m else None,
            problems,
        )
        structural_run.append(DECLARED_STRUCTURAL_CHECKS[2])
        # The command-set comparison lives inside check_install_script_labels, alongside the
        # label comparison it strengthens; it is declared separately because it is a separate
        # promise and must not be able to disappear silently.
        structural_run.append(DECLARED_STRUCTURAL_CHECKS[3])
    else:
        structural_run += list(DECLARED_STRUCTURAL_CHECKS[1:])
    if problems:
        print("check_doc_claims.py: FAIL — the published install script does not hold up",
              file=sys.stderr)
        for problem in problems:
            print(f"  - {problem}", file=sys.stderr)
        return 1

    # ---------------------------------------------------------------- computed reality ----------
    # Order matters here, and it was wrong once. A cold build runs FIRST, and everything else is
    # measured after it. The previous version ran the gate against whatever `.olean`s happened to
    # be lying around, then rebuilt, and then read the constant count out of that first, pre-build
    # gate output — so an edited source with stale `.olean`s produced a green run publishing the
    # numbers of the *old* code. That is a false pass for exactly the claim this script exists to
    # make. One build, then one gate against that build, and every value below comes from after
    # the build.
    build_rc, build_out = run(["bash", "-c", "lake clean && lake build"], root)
    if build_rc != 0:
        print("FAIL: `lake clean && lake build` does not succeed:\n" + build_out, file=sys.stderr)
        return 1
    built_modules = set(re.findall(r"Built (\S+)", build_out))
    jobs = extract(r"\((\d+) jobs\)", build_out, "the lake job count", problems)

    gate_rc, gate_out = run(["./scripts/check_axioms.sh"], root)
    if gate_rc != 0:
        print("FAIL: ./scripts/check_axioms.sh does not pass on the freshly built tree, so there "
              "is no successful transcript to compare the documents against:\n" + gate_out,
              file=sys.stderr)
        return 1

    manifest_rc, manifest_out = run(
        [sys.executable, "scripts/gen_proof_sha256.py", "--check"], root)
    if manifest_rc != 0:
        print("FAIL: the hash manifest is stale, so its published line cannot be checked:\n"
              + manifest_out, file=sys.stderr)
        return 1

    table_rc, table_out = run(
        [sys.executable, "scripts/regression_fixtures.py", "--expected-table"], root)
    if table_rc != 0:
        print("FAIL: scripts/regression_fixtures.py --expected-table failed:\n" + table_out,
              file=sys.stderr)
        return 1

    theorems_rc, theorems_out = run([sys.executable, "scripts/list_theorems.py"], root)
    if theorems_rc != 0:
        print("FAIL: scripts/list_theorems.py failed:\n" + theorems_out, file=sys.stderr)
        return 1

    import regression_fixtures  # noqa: E402  (path set above; this is the roster's own source)

    theorems = len([line for line in theorems_out.splitlines() if line.strip()])
    library_files = sorted((root / "AhlProofs").rglob("*.lean"))
    theorem_files = len(library_files) + 1          # the library plus the root module
    manifest_files = len(
        (root / "reports" / "PROOF.sha256").read_text(encoding="utf-8").splitlines())
    constants = extract(r"scanned (\d+) constant\(s\)", gate_out, "the constant count", problems)
    runs = len(regression_fixtures.DECLARED_RUNS)
    modes = len(regression_fixtures.DECLARED_MODES)

    ci = (root / ".github" / "workflows" / "ci.yml").read_text(encoding="utf-8")
    lean_version = extract(r'EXPECTED_LEAN_VERSION:\s*"([^"]+)"', ci, "the pinned Lean version",
                           problems)
    lean_commit = extract(r'EXPECTED_LEAN_COMMIT:\s*"([^"]+)"', ci, "the pinned release commit",
                          problems)
    linux_digest = extract(r'LEAN_ASSET_SHA256:\s*"([^"]+)"', ci, "the pinned archive digest",
                           problems)
    # The ASSET/DIGEST pair inside reports/TOOLCHAIN.md's install script, which is what a reader
    # actually runs. Only the table above it used to be checked, so a mistyped digest in the
    # script itself would have gone unnoticed — and did, once, before this check existed.
    linux_asset = extract(r'LEAN_ASSET:\s*"([^"]+)"', ci, "the pinned archive name", problems)
    if linux_asset and linux_asset not in LEAN_RELEASE_DIGESTS:
        problems.append(
            f"the archive .github/workflows/ci.yml installs ({linux_asset}) has no digest "
            "recorded in this script"
        )
    elif linux_asset and LEAN_RELEASE_DIGESTS[linux_asset] != linux_digest:
        problems.append(
            f"digest mismatch for {linux_asset}: ci.yml has {linux_digest}, this script has "
            f"{LEAN_RELEASE_DIGESTS[linux_asset]}"
        )

    toolchain_pin = (root / "lean-toolchain").read_text(encoding="utf-8").strip()
    if lean_version and toolchain_pin != f"leanprover/lean4:v{lean_version}":
        problems.append(
            f"lean-toolchain says {toolchain_pin!r} but .github/workflows/ci.yml installs Lean "
            f"{lean_version}"
        )

    if problems:
        print("check_doc_claims.py: FAIL — could not establish what to compare against",
              file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        return 1

    # ---------------------------------------------------------------- transcript claims ---------
    transcripts = [
        ("reports/PROOF.md", "### `./scripts/check_axioms.sh`",
         "the ./scripts/check_axioms.sh transcript",
         "$ ./scripts/check_axioms.sh\n" + gate_out.rstrip("\n")),
        ("reports/PROOF.md",
         "### Binding: what `reports/PROOF.sha256` does and does not give you",
         "the manifest --check line",
         "$ python3 scripts/gen_proof_sha256.py --check\n" + manifest_out.strip()),
        ("reports/PROOF.md", "### Required regression tests",
         "the regression-fixture table", table_out.rstrip("\n")),
    ]
    for doc_name, heading, label, expected in transcripts:
        check_transcript(docs[doc_name], doc_name, heading, expected, label, problems)

    # The build transcript, checked for its reproducible content only: the set of modules built
    # and the job count. Located as a single block in its own section the same way.
    build_heading = "### `lake clean && time lake build`"
    build_hits = [(off, body) for off, body in fenced_blocks(docs["reports/PROOF.md"])
                  if body.splitlines()
                  and body.splitlines()[0].rstrip() == "$ lake clean && time lake build"]
    if len(build_hits) != 1:
        problems.append(
            f"reports/PROOF.md: expected exactly one published `lake clean && time lake build` "
            f"transcript, found {len(build_hits)}"
        )
    else:
        build_off, build_body = build_hits[0]
        # Same section check the other three transcripts get; an earlier version located this one
        # by first line only and threw the offset away, so the promise that it sits in the section
        # named for it was not actually enforced.
        build_span = section_span(docs["reports/PROOF.md"], build_heading)
        if build_span is None:
            problems.append(f"reports/PROOF.md: section {build_heading!r} is gone")
        elif not (build_span[0] <= build_off < build_span[1]):
            problems.append(
                "reports/PROOF.md: the build transcript is published outside the section "
                f"{build_heading!r} it belongs to"
            )
        published_modules = set(re.findall(r"Built (\S+)", build_body))
        published_jobs = re.search(r"\((\d+) jobs\)", build_body)
        if published_modules != built_modules:
            problems.append(
                "reports/PROOF.md: the published build transcript lists modules "
                f"{sorted(published_modules)}, the build produced {sorted(built_modules)}"
            )
        if not published_jobs:
            problems.append(
                "reports/PROOF.md: the published build transcript does not state a job count"
            )
        elif jobs and published_jobs.group(1) != jobs:
            problems.append(
                f"reports/PROOF.md: the published build transcript says "
                f"{published_jobs.group(1)} jobs, lake reports {jobs}"
            )

    # ---------------------------------------------------------------- prose claims --------------
    # (document, pattern, expected values for the pattern's groups, label)
    claims = [
        ("README.md",
         r"\(currently (\d+); not only the (\d+) named `theorem`/`lemma` declarations",
         (constants, str(theorems)), "constant and theorem counts"),
        ("README.md", r"at a finer grain than the (\d+) named\s+theorems",
         (str(theorems),), "theorem count"),
        ("README.md", r"(\d+) fixture runs covering (\d+) failure modes",
         (str(runs), str(modes)), "fixture run and failure-mode counts"),
        ("reports/PROOF.md",
         r"currently (\d+) constants, against the (\d+) named `theorem`/`lemma`",
         (constants, str(theorems)), "constant and theorem counts"),
        ("reports/PROOF.md", r"\s(\d+) constants, not only the (\d+) named theorems",
         (constants, str(theorems)), "constant and theorem counts"),
        ("reports/PROOF.md", r"\((\d+), in (\d+) files", (str(theorems), str(theorem_files)),
         "theorem count and the number of files they live in"),
        ("reports/PROOF.md", r"against all (\d+)\s+constants under", (constants,),
         "constant count"),
        ("reports/PROOF.md", r"(\d+) fixture runs covering (\d+) failure modes",
         (str(runs), str(modes)), "fixture run and failure-mode counts"),
        ("reports/TOOLCHAIN.md", r"(\d+) fixture runs covering (\d+) failure modes",
         (str(runs), str(modes)), "fixture run and failure-mode counts"),
        ("reports/PROOF.md", r"is current \((\d+) file\(s\)\)", (str(manifest_files),),
         "the number of files in the hash manifest"),
        # Anchored on `lean-toolchain`, so the ahl-core / atl-core commit SHAs quoted elsewhere
        # in the same document are not mistaken for the Lean release commit.
        ("reports/PROOF.md", r"`lean-toolchain`, commit `([0-9a-f]{40})`", (lean_commit,),
         "the Lean release commit"),
        ("reports/TOOLCHAIN.md", r"commit ([0-9a-f]{40}), Release", (lean_commit,),
         "the Lean release commit"),
        ("reports/TOOLCHAIN.md", r"EXPECTED_LEAN_VERSION=([0-9.]+)", (lean_version,),
         "the pinned Lean version"),
        ("reports/TOOLCHAIN.md", r"EXPECTED_LEAN_COMMIT=([0-9a-f]{40})", (lean_commit,),
         "the pinned release commit"),
        # The toolchain tag, wherever the documents spell it out.
        ("README.md", r"leanprover/lean4:v([0-9.]+)", (lean_version,), "the pinned toolchain tag"),
        ("reports/PROOF.md", r"leanprover/lean4:v([0-9.]+)", (lean_version,),
         "the pinned toolchain tag"),
        ("reports/TOOLCHAIN.md", r"leanprover/lean4:v([0-9.]+)", (lean_version,),
         "the pinned toolchain tag"),
        # The version inside the recorded `lean --version` line at the top of TOOLCHAIN.md.
        ("reports/TOOLCHAIN.md", r"Lean \(version ([0-9.]+),", (lean_version,),
         "the version in the recorded toolchain self-report"),
        # Every `N jobs` figure, against what lake reported on the cold build above.
        ("reports/PROOF.md", r"\((\d+) jobs\)", (jobs,), "the lake job count"),
        ("reports/PROOF.md", r"all (\d+) jobs", (jobs,), "the lake job count"),
        ("reports/TOOLCHAIN.md", r"`?(\d+) jobs`?", (jobs,), "the lake job count"),
    ] + [
        # Every platform archive digest offered by TOOLCHAIN.md, not only the one CI installs.
        ("reports/TOOLCHAIN.md",
         r"`" + re.escape(asset) + r"` \| `([0-9a-f]{64})`", (digest,),
         f"the {asset} digest")
        for asset, digest in LEAN_RELEASE_DIGESTS.items()
    ]
    # The rosters, before any of it is used. A shortened `transcripts` or `claims` must be a
    # failure, not a shorter but passing run.
    expected_labels = set(DECLARED_CLAIM_LABELS) | {
        f"the {asset} digest" for asset in LEAN_RELEASE_DIGESTS
    }
    actual_labels = {label for _, _, _, label in claims}
    roster_problems = []
    if tuple(structural_run) != DECLARED_STRUCTURAL_CHECKS:
        roster_problems.append(
            f"structural-check set does not match the declared one: expected "
            f"{list(DECLARED_STRUCTURAL_CHECKS)}, got {structural_run}"
        )
    if tuple(label for _, _, label, _ in transcripts) != DECLARED_TRANSCRIPTS:
        roster_problems.append(
            f"transcript set does not match the declared one: expected "
            f"{list(DECLARED_TRANSCRIPTS)}, got {[label for _, _, label, _ in transcripts]}"
        )
    if actual_labels != expected_labels:
        roster_problems.append(
            "claim set does not match the declared one; missing "
            f"{sorted(expected_labels - actual_labels)}, unexpected "
            f"{sorted(actual_labels - expected_labels)}"
        )
    if roster_problems:
        print("check_doc_claims.py: FAIL — this checker is not checking what it declares",
              file=sys.stderr)
        for problem in roster_problems:
            print(f"  - {problem}", file=sys.stderr)
        return 1

    for doc_name, pattern, expected_groups, label in claims:
        matches = re.findall(pattern, docs[doc_name])
        if not matches:
            problems.append(
                f"{doc_name}: no occurrence of {label} found (pattern {pattern!r}) — a claim that "
                "cannot be located is not a claim that has been checked; if the wording changed, "
                "this pattern has to change with it"
            )
            continue
        for m in matches:
            got = (m,) if isinstance(m, str) else tuple(m)
            if got != expected_groups:
                problems.append(
                    f"{doc_name}: {label} says {got}, the checks say {expected_groups}"
                )

    # ---------------------------------------------------------------- fixture roster -------------
    proof = docs["reports/PROOF.md"]
    # Only the fixture table, not the lemma-clause tables elsewhere in the same document.
    section = re.search(
        r"### Required regression tests\n(.*?)\n### ", proof, flags=re.S)
    if not section:
        problems.append(
            'reports/PROOF.md: the "Required regression tests" section is gone — the fixture '
            "roster has nothing to be checked against"
        )
        section_text = ""
    else:
        section_text = section.group(1)
    table_ids = re.findall(r"^\| (\d[0-9a-z]*) \| ", section_text, flags=re.M)
    declared = list(regression_fixtures.DECLARED_RUNS)
    if table_ids != declared:
        problems.append(
            f"reports/PROOF.md: the fixture table lists {table_ids}, but "
            f"scripts/regression_fixtures.py declares {declared}"
        )

    if problems:
        print("check_doc_claims.py: FAIL — the documents disagree with the checks",
              file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        print(
            "\nEvery number and transcript above is generated by a command in this repository. "
            "Rerun the command, paste what it prints, and this passes.",
            file=sys.stderr,
        )
        return 1

    print(
        f"document claims hold: {len(DECLARED_STRUCTURAL_CHECKS)} structural check(s) on the "
        f"published install script passed (single block, sh -n, CI step labels and command sets "
        f"against all {len(ci_steps)} workflow steps, and the platform-selection block parsed "
        f"and checked for exactly {len(DECLARED_PLATFORM_BRANCHES)} declared branches); "
        f"{len(transcripts)} published transcript(s) matched exactly (one "
        f"block each, in its own section); the build transcript matched on modules "
        f"({len(built_modules)}) and job count ({jobs}); {len(claims)} numeric/pin claim(s) "
        f"matched ({theorems} theorems in {theorem_files} files, {constants} constants, "
        f"{manifest_files} files in the manifest, {runs} fixture runs covering {modes} failure "
        f"modes, {len(LEAN_RELEASE_DIGESTS)} release digests, Lean {lean_version} commit "
        f"{lean_commit[:12]}…)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
