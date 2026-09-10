#!/usr/bin/env python3
"""Import invariant: every `AhlProofs/**/*.lean` file in the working tree must be reachable, by
imports, from the library root module `AhlProofs.lean`.

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

    unreachable = sorted(set(found) - reachable)
    for mod in unreachable:
        problems.append(
            f"{found[mod].relative_to(root)} is not reachable by imports from {ROOT_FILE} — "
            f"it is never built, so `scripts/Audit.lean` never sees it. Add "
            f"`import {mod}` to {ROOT_FILE} (or to a module already imported from it)."
        )

    if problems:
        print("check_imports.py: FAIL — the import invariant does not hold", file=sys.stderr)
        for p in problems:
            print(f"  - {p}", file=sys.stderr)
        print(
            "\nEvery .lean file under AhlProofs/ must be reachable by imports from "
            f"{ROOT_FILE}; otherwise `lake build` and the axiom audit both pass while ignoring "
            "it entirely.",
            file=sys.stderr,
        )
        return 1

    print(
        f"import invariant holds: {len(found)} file(s) under {LIBRARY_DIR}/, all reachable "
        f"from {ROOT_FILE} ({len(reachable)} module(s) in the transitive closure)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
