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
import subprocess
import sys


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
        f"document claims hold: {len(transcripts)} published transcript(s) matched exactly (one "
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
