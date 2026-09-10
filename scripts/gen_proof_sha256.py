#!/usr/bin/env python3
"""Generate (or check) `reports/PROOF.sha256` — an internal-consistency manifest over every file
that participates in the Lean build, the audit tooling, or the CI workflow that runs both: the
toolchain pin, the lake project files, every `.lean` file under the library (discovered the same
way `scripts/list_theorems.py` discovers them — a glob, not a hand-maintained list, so a *new*
`.lean` file is picked up automatically), every audit script, and `.github/workflows/ci.yml`
itself — the workflow is what determines whether the audit runs at all, so a manifest that did
not cover it would not notice a change that quietly deleted the audit step.

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
`reports/PROOF.md` and `reports/TOOLCHAIN.md` are prose that can be edited without touching what
the build or the audit compute, and are not included. What is included is exactly the set of
files whose content changes what CI computes — the previous version of this file was a
hand-written list that a new `.lean` file did not have to join to build; this generator has no
such gap because it does not hand-maintain a list.

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


def discover(root: pathlib.Path) -> list[pathlib.Path]:
    paths = [root / f for f in FIXED_FILES]
    paths += sorted((root / "AhlProofs").rglob("*.lean"))
    paths += sorted((root / "scripts").glob("*.py"))
    paths += sorted((root / "scripts").glob("*.sh"))
    paths += sorted((root / "scripts").glob("*.lean"))
    return [p for p in paths if p.is_file()]


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

    fresh = manifest_lines(root)
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
