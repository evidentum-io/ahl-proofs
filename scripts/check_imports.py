#!/usr/bin/env python3
"""Lean-file coverage: every `.lean` in this repository belongs to a declared category, and every
library module is reachable by imports from the root module `AhlProofs.lean`.

Two rules, and the first one exists because the second was not enough. See `DECLARED_AUXILIARY`
below for why the coverage rule is stated as "everything must be classified" rather than as one
more directory to walk.

**Why this exists.** `scripts/Audit.lean` audits the compiled `Lean.Environment` produced by
`import AhlProofs`, which is exactly the right thing to audit — but it can only see what was
*built*, and what gets built is what the root module transitively imports. That import list is
maintained by hand. A `.lean` file that nobody imports is therefore not a build failure and not
an audit finding: it is simply absent from both. `lake build` exits 0, the axiom audit exits 0,
and a file containing anything at all — `axiom planted_bad : False` included — sits in the
repository unexamined.

That is not an exotic attack; it is ordinary forgetfulness. Adding `AhlProofs/Foo.lean` and
forgetting the matching `import AhlProofs.Foo` line produces a repository whose green CI says
nothing whatever about `Foo.lean`, and nothing in the pipeline noticed. This check closes the
gap by comparing two independently obtained sets:

* **found** — every `*.lean` file under `AhlProofs/`, discovered by a filesystem glob;
* **reachable** — the transitive closure of `import AhlProofs.*` lines starting at
  `AhlProofs.lean`.

They must be equal. A file in `found` but not in `reachable` is unbuilt and unaudited. A module
in `reachable` but not in `found` is an import of a library module whose file does not exist
(which `lake build` would also catch, but this check names it precisely and earlier).

**What this does not do.** It is a structural check, not a semantic one: it establishes that
everything present is compiled and therefore reaches `scripts/Audit.lean`, not that what was
compiled proves anything. And, like every check in this repository, it lives in the repository
it checks — see "Trust boundary" in `reports/PROOF.md`.

Usage:
    check_imports.py [--root DIR]     # exit 0 if the invariant holds, 1 otherwise
"""
import argparse
import pathlib
import re
import sys

LIBRARY_DIR = "AhlProofs"
ROOT_MODULE = "AhlProofs"
ROOT_FILE = "AhlProofs.lean"
# The three directories that hold no repository source: git's own storage, lake's build output,
# and Python bytecode caches. Nothing under them is written by a person, and — checked, not
# assumed — none of them contains a single `.lean` file in this project, which takes no
# dependencies and so never has Lake place sources under `.lake/`.
#
# They are **not** a hole in the coverage rule below, and this is the fourth shape of that hole to
# turn up: `axiom hidden_in_pycache : False` in `__pycache__/Bad.lean` used to pass every check
# while layer 1 printed "0 unclassified". Excluding a directory from classification is the same
# mistake as forgetting to include one. So a `.lean` under any of these is not classified — it is
# **refused**, because there is no legitimate way for one to be there.
#
# This is the single definition of the controlled area. `scripts/check_source_policy.py` and
# `scripts/regression_fixtures.py` import it rather than repeating it, so the three walks over the
# tree cannot drift apart.
EXCLUDED_DIRS = {".git", ".lake", "__pycache__"}

# What this repository calls a Lean file: a regular file whose name ends in exactly `.lean`.
#
# Said precisely because the guarantee should not read wider than the code. A file whose suffix
# merely case-folds to `.lean` (`Bad.LEAN`) is rejected outright below rather than quietly
# uncovered — Lean sources here are lower-case by convention and a variant spelling is either a
# mistake or an attempt to slip past a suffix match. A file with Lean *content* and no `.lean`
# suffix is outside this guarantee and outside every other check here: nothing in this repository
# reads file contents to guess a language, and this document does not pretend otherwise.
LEAN_SUFFIX = ".lean"

# Every `.lean` file in this repository that is **not** part of the proof library, declared one by
# one. Nothing else may exist.
#
# This list closes a class rather than a case. Three times now a file has turned out to sit
# somewhere no check looked: under `AhlProofs/` but imported by nobody; under `scripts/` in a
# subdirectory a non-recursive glob missed; and finally in the repository root, where an
# `axiom planted_at_root : False` passed the manifest, the import invariant, the source policy,
# `lake build` and the whole gate, because every one of them walked a *chosen* directory. Widening
# the walk by one directory each time is how a fourth place stays available. So the rule is
# inverted here: every `.lean` anywhere in the working tree must fall into one of exactly two
# declared categories —
#
#   * a **library module**: `AhlProofs.lean` or a file under `AhlProofs/`. It must be reachable by
#     imports from the root module, which makes it built, hashed by the manifest and walked by the
#     environment audit.
#   * a **declared auxiliary file**: named below. Auxiliary files are not part of the library and
#     are never elaborated, so an `axiom` in one is inert; they are covered by the hash manifest
#     and by the source policy, and by nothing else, which is precisely why each has to be named
#     rather than admitted by directory.
#
# Anything else fails, with its path and what to do about it. A new auxiliary file is a one-line
# change here, made deliberately, instead of a silently uncovered file.
DECLARED_AUXILIARY = ("scripts/Audit.lean",)

# `import Foo.Bar`, tolerating the modifiers Lean 4 allows in front of, and inside, an import
# line (`public import`, `import all Foo`). A line that begins with the keyword `import` but does
# not match is reported as an error rather than skipped: silently ignoring an import line this
# parser does not understand is exactly the kind of quiet gap this file exists to close.
IMPORT_RE = re.compile(
    r"^(?:(?:public|private|meta|protected)\s+)*import\s+(?:all\s+)?"
    r"([A-Za-z_][A-Za-z0-9_'À-ɏͰ-Ͽ]*"
    r"(?:\.[A-Za-z_][A-Za-z0-9_'À-ɏͰ-Ͽ]*)*)\s*$"
)


def module_of(path: pathlib.Path, root: pathlib.Path) -> str:
    """`AhlProofs/Tree/Model.lean` (relative to the repo root) ↦ `AhlProofs.Tree.Model`."""
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def file_of(module: str, root: pathlib.Path) -> pathlib.Path:
    return root.joinpath(*module.split(".")).with_suffix(".lean")


def header_imports(path: pathlib.Path) -> tuple[list[str], list[str]]:
    """Return (imported module names, errors).

    Lean requires every `import` to precede all other commands in a file, so only the header is
    read: scanning stops at the first line that is neither blank, nor a comment, nor an import.
    Block comments (`/- -/`, nesting included, which covers `/-- -/` and `/-! -/`) and line
    comments are skipped. String literals are deliberately *not* modelled — a `/-` inside a
    string literal in a file's import header would confuse this reader, but a file whose header
    contains a string literal at all is already not a valid Lean header, so the failure mode is
    a parse error here rather than a silent omission.
    """
    errors: list[str] = []
    imports: list[str] = []
    depth = 0
    for lineno, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
        kept: list[str] = []
        i, n = 0, len(raw)
        while i < n:
            two = raw[i:i + 2]
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
                break
            kept.append(raw[i])
            i += 1
        code = "".join(kept).strip()
        if not code:
            continue
        m = IMPORT_RE.match(code)
        if m:
            imports.append(m.group(1))
            continue
        if code.split(maxsplit=1)[0] in ("import", "public", "private", "meta", "protected") \
                and "import" in code:
            errors.append(
                f"{path}:{lineno}: import line not understood by this checker: {code!r} — "
                "the import invariant cannot be established while an import line is unparsed"
            )
            continue
        break
    return imports, errors


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=".", help="repository root (default: cwd)")
    args = ap.parse_args()
    root = pathlib.Path(args.root).resolve()

    problems: list[str] = []

    root_file = root / ROOT_FILE
    if not root_file.is_file():
        print(f"FAIL: library root module {ROOT_FILE} does not exist under {root}",
              file=sys.stderr)
        return 1

    found = {module_of(p, root): p for p in sorted((root / LIBRARY_DIR).rglob("*.lean"))}
    if not found:
        print(f"FAIL: no .lean files found under {root / LIBRARY_DIR} — refusing to report "
              "success on an empty library", file=sys.stderr)
        return 1

    # Transitive closure of imports from the root module.
    reachable: set[str] = set()
    queue = [ROOT_MODULE]
    seen_files: dict[str, pathlib.Path] = {ROOT_MODULE: root_file}
    while queue:
        mod = queue.pop()
        if mod in reachable:
            continue
        reachable.add(mod)
        path = seen_files.get(mod) or file_of(mod, root)
        if not path.is_file():
            problems.append(
                f"module `{mod}` is imported but has no file — expected "
                f"{path.relative_to(root) if path.is_relative_to(root) else path}"
            )
            continue
        imports, errors = header_imports(path)
        problems.extend(errors)
        for imp in imports:
            # Only this library's own modules participate; `import Lean`, `import Init.…` and
            # anything else on the search path is outside the invariant by construction.
            if imp == ROOT_MODULE or imp.startswith(ROOT_MODULE + "."):
                if imp not in reachable:
                    queue.append(imp)

    # ---- the coverage rule: every .lean in the tree belongs to a declared category ------------
    declared_aux = set(DECLARED_AUXILIARY)
    for rel in sorted(declared_aux):
        if not (root / rel).is_file():
            problems.append(
                f"{rel} is declared as an auxiliary Lean file but does not exist — a declaration "
                "that names nothing is how this list stops meaning anything"
            )
    # A symlinked directory would make "this repository's files" mean whatever it points at, and
    # would put reachability outside the tree's control. There are none, and there is no use for
    # one here. `.git` is left out of this scan only because git itself may legitimately use links
    # in its own storage; nothing under `.git` is a Lean source, and the scan below refuses one
    # anyway.
    for q in sorted(root.rglob("*")):
        parts = set(q.relative_to(root).parts)
        if ".git" in parts:
            continue
        if q.is_symlink() and q.is_dir():
            problems.append(
                f"{q.relative_to(root)} is a symbolic link to a directory. This repository "
                "contains none, and one would make the set of files it covers depend on "
                "something outside it."
            )

    # Every `.lean` in the tree, excluded directories included: a file under one of them is not
    # classified, it is refused. Case variants of the suffix are refused too, so that a coverage
    # rule keyed on the exact suffix cannot be stepped around by spelling it differently.
    all_lean: list[pathlib.Path] = []
    for q in sorted(root.rglob("*")):
        if not q.is_file() or q.is_symlink():
            continue
        suffix = q.suffix
        if suffix.lower() != LEAN_SUFFIX:
            continue
        if suffix != LEAN_SUFFIX:
            problems.append(
                f"{q.relative_to(root)} spells the Lean suffix as {suffix!r}. Lean sources in "
                f"this repository are named {LEAN_SUFFIX!r}; a variant spelling is either a "
                "mistake or a way past a suffix match, and is refused either way."
            )
            continue
        all_lean.append(q)

    forbidden_area = [
        q for q in all_lean if EXCLUDED_DIRS & set(q.relative_to(root).parts)
    ]
    for q in forbidden_area:
        problems.append(
            f"{q.relative_to(root)} is a Lean file under a directory that holds no Lean source in "
            f"this project ({', '.join(sorted(EXCLUDED_DIRS))}). Those directories are git's own "
            "storage, lake's build output and Python bytecode caches; a `.lean` there is either a "
            "mistake or an attempt to keep code out of classification. Remove it, or move it "
            f"under {LIBRARY_DIR}/ and import it."
        )

    every_lean = [q for q in all_lean if q not in set(forbidden_area)]
    library_rels = {str(q.relative_to(root)) for q in found.values()} | {ROOT_FILE}
    unclassified = [
        str(q.relative_to(root)) for q in every_lean
        if str(q.relative_to(root)) not in library_rels
        and str(q.relative_to(root)) not in declared_aux
    ]
    for rel in unclassified:
        problems.append(
            f"{rel} is a Lean file that belongs to no declared category. Every .lean in this "
            f"repository must be either a library module ({ROOT_FILE} or a file under "
            f"{LIBRARY_DIR}/, reachable by imports, hence built, hashed and audited) or a "
            "declared auxiliary file listed in DECLARED_AUXILIARY in this script. As it stands "
            "nothing builds, hashes or audits this file: move it under "
            f"{LIBRARY_DIR}/ and import it, or declare it."
        )

    unreachable = sorted(set(found) - reachable)
    for mod in unreachable:
        problems.append(
            f"{found[mod].relative_to(root)} is not reachable by imports from {ROOT_FILE} — "
            f"it is never built, so `scripts/Audit.lean` never sees it. Add "
            f"`import {mod}` to {ROOT_FILE} (or to a module already imported from it)."
        )

    if problems:
        print("check_imports.py: FAIL — some Lean file is not covered as it must be",
              file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        print(
            "\nEvery .lean file in this repository must be either a library module under "
            f"{LIBRARY_DIR}/ reachable by imports from {ROOT_FILE} — otherwise `lake build` and "
            "the axiom audit both pass while ignoring it entirely — or a file named in "
            "DECLARED_AUXILIARY. There is no third place for one to sit.",
            file=sys.stderr,
        )
        return 1

    print(
        f"every .lean accounted for: {len(found)} library module(s) under {LIBRARY_DIR}/, all "
        f"reachable from {ROOT_FILE} ({len(reachable)} module(s) in the closure); "
        f"{len(declared_aux)} declared auxiliary file(s); 0 unclassified"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
