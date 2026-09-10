#!/usr/bin/env python3
"""Generate (or check) `reports/PROOF.sha256` — an internal-consistency manifest over every file
that participates in the Lean build, the audit tooling, or the CI workflow that runs both: the
toolchain pin, the lake project files, every `.lean` file under the library (discovered by a
recursive glob, not a hand-maintained list, so a *new* `.lean` file is picked up automatically),
every audit script under `scripts/` **at any depth**, and `.github/workflows/ci.yml` itself — the
workflow is what determines whether the audit runs at all, so a manifest that did not cover it
would not notice a change that quietly deleted the audit step.

Every one of those is **required to exist**. A missing entry is a failure of this script, not a
shorter manifest: see `discover()` for why that distinction is the whole point.

**What this manifest is, and is not.** It is a same-commit internal-consistency check: the
manifest is generated from, and committed alongside, exactly the files it lists, by the same
process (a person or CI run editing this repository) that could edit any of them. It does not
"bind the exact content" of anything in the sense of proving integrity or provenance against a
party who can alter the repository — there is no external anchor, no signature, and no
timestamp from outside this commit. What it *does* give is protection against silent drift
inside a single change: if any listed file's bytes change without `reports/PROOF.sha256` being
regenerated to match, `--check` fails, so a file cannot fall out of sync with what the manifest
claims about it merely by someone forgetting to rerun this script.

This is deliberately narrower than "every file in the repository": `README.md`,
`reports/PROOF.md` and `reports/TOOLCHAIN.md` are not included. What is included is the set of
files whose content changes **what the build produces, what the audit walks, or the structure of
the workflow that runs them** — the previous version of this file was a hand-written list that a
new `.lean` file did not have to join to build; this generator has no such gap because it does
not hand-maintain a list.

Not "everything that changes the outcome of CI", which would be wider and false as written: the
three prose documents are unhashed and can still turn CI red, because `scripts/check_doc_claims.py`
compares their numbers and transcripts against what the checks print. They are covered by that
check rather than by this manifest, and the distinction is the point — hashing them would make
every wording change a manifest regeneration for no gain.

Usage:
    gen_proof_sha256.py            # print the manifest to stdout, sha256sum -c format
    gen_proof_sha256.py --check    # exit nonzero (with a diff) if reports/PROOF.sha256 is stale
"""
import argparse
import difflib
import hashlib
import pathlib
import sys

FIXED_FILES = [
    "lean-toolchain",
    "lakefile.toml",
    "lake-manifest.json",
    "AhlProofs.lean",
    ".github/workflows/ci.yml",
]


# The smallest set that still means something. A manifest listing fewer files than this is not a
# smaller manifest, it is a broken one, and it must not be generated or accepted.
MIN_LIBRARY_FILES = 1
MIN_SCRIPT_FILES = 1


class Degenerate(Exception):
    """The discovered set is missing something the manifest is documented to cover."""


def discover(root: pathlib.Path) -> list[pathlib.Path]:
    """Every file the manifest covers, or `Degenerate` if any of it is missing.

    **Why this raises instead of filtering.** An earlier version ended in
    `return [p for p in paths if p.is_file()]`: a file named in `FIXED_FILES` that did not exist
    simply dropped out of the set. On a tree with none of them present, and an empty
    `reports/PROOF.sha256`, `--check` compared `[]` against `[]` and reported success — having
    verified nothing, while this module's docstring went on promising that the toolchain pin, the
    lake project files and every audit script were covered. That is the same defect as an audit
    whose target list can be truncated to empty and still pass, and it is the third time this
    repository has grown one. A set built by filtering and then compared against a manifest built
    the same way must treat a degenerate set as failure, never as agreement.

    `rglob` is used for `scripts/` as well as for the library: the documentation promises *every*
    audit script, and an earlier `glob` covered only the immediate directory, so a script in a
    subdirectory would have gone unhashed while the prose said otherwise. Regression fixture 8
    exercises exactly that.
    """
    missing = [f for f in FIXED_FILES if not (root / f).is_file()]
    if missing:
        raise Degenerate(
            "file(s) this manifest is required to cover do not exist: " + ", ".join(missing)
        )

    library = sorted((root / "AhlProofs").rglob("*.lean"))
    if len(library) < MIN_LIBRARY_FILES:
        raise Degenerate(
            f"found {len(library)} .lean file(s) under AhlProofs/, expected at least "
            f"{MIN_LIBRARY_FILES} — a manifest covering no proof source is not a manifest"
        )

    scripts: list[pathlib.Path] = []
    for pattern in ("*.py", "*.sh", "*.lean"):
        scripts += (root / "scripts").rglob(pattern)
    scripts = sorted(set(scripts))
    if len(scripts) < MIN_SCRIPT_FILES:
        raise Degenerate(
            f"found {len(scripts)} file(s) under scripts/, expected at least {MIN_SCRIPT_FILES} — "
            "a manifest covering no audit tooling is not a manifest"
        )

    paths = [root / f for f in FIXED_FILES] + library + scripts
    not_files = [str(p.relative_to(root)) for p in paths if not p.is_file()]
    if not_files:
        raise Degenerate("discovered path(s) that are not readable files: " + ", ".join(not_files))
    return paths


def manifest_lines(root: pathlib.Path) -> list[str]:
    lines = []
    for p in discover(root):
        digest = hashlib.sha256(p.read_bytes()).hexdigest()
        lines.append(f"{digest}  {p.relative_to(root)}")
    return lines


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".")
    ap.add_argument(
        "--check",
        action="store_true",
        help="compare against reports/PROOF.sha256 instead of printing",
    )
    args = ap.parse_args()
    root = pathlib.Path(args.root).resolve()

    try:
        fresh = manifest_lines(root)
    except Degenerate as e:
        # Before any comparison: an incomplete set must fail, whether generating or checking.
        # Comparing an incomplete set against a manifest generated from the same incomplete set
        # would agree, and agreeing on nothing is exactly what this guards against.
        print(f"FAIL: refusing to work with a degenerate file set — {e}", file=sys.stderr)
        return 1
    if not args.check:
        print("\n".join(fresh))
        return 0

    recorded_path = root / "reports" / "PROOF.sha256"
    if not recorded_path.is_file():
        print(f"FAIL: {recorded_path} does not exist", file=sys.stderr)
        return 1
    recorded = recorded_path.read_text(encoding="utf-8").splitlines()

    if fresh == recorded:
        print(f"reports/PROOF.sha256 is current ({len(fresh)} file(s))")
        return 0

    print("FAIL: reports/PROOF.sha256 is stale — run", file=sys.stderr)
    print("  python3 scripts/gen_proof_sha256.py > reports/PROOF.sha256", file=sys.stderr)
    print("and commit the result. Diff (recorded -> current):", file=sys.stderr)
    diff = difflib.unified_diff(recorded, fresh, lineterm="", fromfile="recorded", tofile="current")
    for line in diff:
        print(line, file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
