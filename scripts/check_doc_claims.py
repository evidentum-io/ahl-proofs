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


def run(cmd: list[str], cwd: pathlib.Path) -> tuple[int, str]:
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return proc.returncode, proc.stdout + proc.stderr


def extract(pattern: str, text: str, label: str, problems: list[str]) -> str | None:
    m = re.search(pattern, text)
    if not m:
        problems.append(f"could not read {label} out of the command output — pattern {pattern!r}")
        return None
    return m.group(1)


def block_diff(doc: str, expected: str) -> str:
    """Best-effort diff between `expected` and the fenced block in `doc` that starts like it."""
    first = expected.splitlines()[0]
    for block in re.findall(r"```[a-z]*\n(.*?)```", doc, flags=re.S):
        if block.splitlines() and block.splitlines()[0].rstrip() == first.rstrip():
            return "\n".join(
                difflib.unified_diff(
                    block.rstrip("\n").splitlines(),
                    expected.splitlines(),
                    lineterm="",
                    fromfile="published in the document",
                    tofile="printed by the command now",
                )
            )
    return "(no fenced block in the document starts with that line at all)"


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
    gate_rc, gate_out = run(["./scripts/check_axioms.sh"], root)
    if gate_rc != 0:
        print("FAIL: ./scripts/check_axioms.sh does not pass, so there is no successful "
              "transcript to compare the documents against:\n" + gate_out, file=sys.stderr)
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
        ("reports/PROOF.md", "the ./scripts/check_axioms.sh transcript",
         "$ ./scripts/check_axioms.sh\n" + gate_out.rstrip("\n")),
        ("reports/PROOF.md", "the manifest --check line",
         "$ python3 scripts/gen_proof_sha256.py --check\n" + manifest_out.strip()),
        ("reports/PROOF.md", "the regression-fixture table", table_out.rstrip("\n")),
    ]
    for doc_name, label, expected in transcripts:
        if expected not in docs[doc_name]:
            problems.append(
                f"{doc_name}: {label} is not what the command prints now.\n"
                + block_diff(docs[doc_name], expected)
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
        ("reports/TOOLCHAIN.md", r"`lean-4\.[0-9.]+-linux\.tar\.zst` \| `([0-9a-f]{64})`",
         (linux_digest,), "the Linux archive digest"),
    ]
    if not claims:
        print("check_doc_claims.py: FAIL — no claims registered", file=sys.stderr)
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
        f"document claims hold: {len(transcripts)} published transcript(s) match their commands "
        f"verbatim; {len(claims)} numeric/pin claim(s) match the checks "
        f"({theorems} theorems in {theorem_files} files, {constants} constants, "
        f"{manifest_files} files in the manifest, {runs} fixture runs covering {modes} failure "
        f"modes, Lean {lean_version} commit {lean_commit[:12]}…)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
