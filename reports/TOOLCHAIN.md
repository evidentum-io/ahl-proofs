# Toolchain

Recorded 2026-09-09 on aarch64-apple-darwin. `.github/workflows/ci.yml` re-establishes the same pin, by the same checks, on `ubuntu-latest` on every push and pull request.

| Component | Pin | What ran here |
|---|---|---|
| Lean | `leanprover/lean4:v4.31.0` in `lean-toolchain`; the operative pin is the release archive SHA-256 recorded under "Install" | local: `Lean (version 4.31.0, arm64-apple-darwin24.6.0, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)` |
| Lake | bundled with the Lean 4.31.0 toolchain | `/opt/homebrew/bin/lake` (local, see the note in "Install"); CI uses the `lake` shipped in the checksummed release archive |
| Dependencies | none | `lake-manifest.json` — `"packages": []`; **no Mathlib**. See "Why no Mathlib" below. |
| OS (this record) | aarch64-apple-darwin (macOS) | CI additionally runs on `ubuntu-latest` |

There is no Rust/Charon/Aeneas layer in this repository. `ahl-proofs` is Lean-only: a model of
the three AHL invariants (`AhlProofs/Model.lean`, `AhlProofs/Closure/Model.lean`,
`AhlProofs/Tree/Model.lean`) and hand-written proofs over it. Nothing here is extracted from
`ahl-core`'s Rust source — see "Relationship to the reference implementation" in `README.md` and
the boundary files for exactly what does and does not connect the two.

## Why no Mathlib

Deliberate, and re-checked at every lemma (`README.md`, "Build"): the three lemmas turned out to
need only facts Lean's own prelude (`Init`) already provides — `List.append_inj`,
`List.cons.injEq`, `List.mem_cons_of_mem` for Lemma 1; two short home-grown finite-set lemmas
(`length_filter_lt_of_witness`, `nub`) for Lemma 2; `Nat.log2_self_le`, `Nat.lt_log2_self`,
`Nat.two_pow_pos`, `Nat.pow_le_pow_right` for Lemma 3's RFC 9162 split-point arithmetic. A
dependency-free build is faster to check and easier to audit end to end, so it is kept that way
for as long as the lemmas allow it.

## Install — the same procedure a human runs and CI runs

The toolchain is installed from the official release **archive**, fetched by its versioned
release URL and compared against a recorded SHA-256 **before** it is unpacked. `lean --version`
is checked afterwards as a diagnostic, not as the identity check.

**Run the file below as a file, not by pasting lines into a shell.** It is written with `set -eu`
and *exits nonzero* at the first failure — a stale hash manifest, an unimported module, a
forbidden lexeme, a `lean-toolchain` that has drifted from the pinned release, a digest mismatch,
the wrong `lean` on `PATH`, a version or release-commit mismatch, or any failing check — with the
same pinned URL, the same comparisons, the same expected values and **the same order** as the
`lean` job of `.github/workflows/ci.yml`. Each block carries the number of the CI step it
corresponds to, so the correspondence can be read off rather than taken on trust. Pasted line by
line the script would print the same output and stop at nothing, which is why it is a file and why
every guard is `exit 1` rather than a printed warning.

Four earlier versions of this section each got that wrong differently, which is why the point is
laboured here: the first piped an installer from a mutable branch with no comparison at all; the
second verified the archive and then let the reader build with whatever `lean` was already on
their `PATH`; the third added guards for exactly that and wrote them as `|| echo`, so they printed
a warning and returned success; the fourth claimed to run CI's steps in CI's order while actually
running only the manifest before the install and never cross-checking the pin at all — so a
repointed `lean-toolchain` passed locally and failed in CI, which is the one outcome this section
exists to prevent.

The four archives this repository records, with the SHA-256 of each. **The script below picks
the right one from `uname -s` and `uname -m`; you do not choose.** A platform not in this table
makes it exit 1 saying so, rather than installing whichever archive happens to be written down
first — which is what an earlier version did, hard-wiring one platform's pair and so handing a
reader on Linux a macOS build while calling the procedure equivalent to CI's.

| Platform | Archive (all under `https://github.com/leanprover/lean4/releases/download/v4.31.0/`) | SHA-256 |
|---|---|---|
| Linux x86-64 (what CI uses) | `lean-4.31.0-linux.tar.zst` | `07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f` |
| Linux aarch64 | `lean-4.31.0-linux_aarch64.tar.zst` | `b1bf1d3c586b76cf4a86212a595d8b9edd99f438a41cce85d5780fa9347c811b` |
| macOS aarch64 (Apple silicon; the machine this file records) | `lean-4.31.0-darwin_aarch64.tar.zst` | `264105500c8abdf37b68ffe03390a783ed259807807222698da8dd92d6ce0a27` |
| macOS x86-64 | `lean-4.31.0-darwin.tar.zst` | `6dac7a8f9d6d0bc339b4ea9376c06a88f3fd1a7f462beb3c7ded9fbc934f3fb5` |

**One script, fail-closed, start to finish.** Everything below is a single runnable file. It runs
the three checks that need no toolchain first — the hash manifest, the import invariant, the source
policy — then cross-checks `lean-toolchain` against the release it is about to install, then
installs that release into one fixed, version-named directory (`$HOME/.local/lean-4.31.0`) after
comparing its digest, puts that directory on `PATH`, refuses to continue unless the `lean` that
resolves is that one and reports the expected release commit, and only then builds and runs the
remaining checks. That is CI's order, step for step.

It is one file on purpose. An earlier version split it into a script plus two follow-up guards
written as `|| echo`, which printed a warning and returned success — so a reader whose `PATH`
pointed at some other Lean would see one line scroll past and build with it anyway. A guard that
does not stop is not a guard, and a procedure a reader can half-perform is not equivalent to a CI
job that fails.

Save this as `verify-ahl-proofs.sh` and run it with `sh verify-ahl-proofs.sh /path/to/ahl-proofs`:

```sh
#!/bin/sh
# Install the pinned Lean toolchain, verify it, and run every check this repository publishes,
# in the same order as the `lean` job of .github/workflows/ci.yml. The step numbers below are
# that job's step numbers. Exits nonzero at the first failure; nothing after a failure runs.
set -eu

# CI step 1 [actions/checkout]. In CI this is the checkout; locally, the clone you have.
REPO="${1:-.}"
cd "${REPO}"

# --- the pinned release; change these two together, never one alone -------------------------
EXPECTED_LEAN_VERSION=4.31.0
EXPECTED_LEAN_COMMIT=68218e876d2a38b1985b8590fff244a83c321783

PREFIX="$HOME/.local/lean-${EXPECTED_LEAN_VERSION}"

# --- platform selection ---------------------------------------------------------------------
# Every archive in the table above, with its recorded SHA-256, chosen by uname. An unrecognised
# platform is an error, never a default: installing "whichever archive was written down first"
# is how a reader on Linux ends up unpacking a macOS build, which is what an earlier version of
# this script did by hard-wiring one platform's pair.
case "$(uname -s)/$(uname -m)" in
  Linux/x86_64)
    ASSET=lean-4.31.0-linux.tar.zst
    DIGEST=07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f
    ;;
  Linux/aarch64 | Linux/arm64)
    ASSET=lean-4.31.0-linux_aarch64.tar.zst
    DIGEST=b1bf1d3c586b76cf4a86212a595d8b9edd99f438a41cce85d5780fa9347c811b
    ;;
  Darwin/arm64)
    ASSET=lean-4.31.0-darwin_aarch64.tar.zst
    DIGEST=264105500c8abdf37b68ffe03390a783ed259807807222698da8dd92d6ce0a27
    ;;
  Darwin/x86_64)
    ASSET=lean-4.31.0-darwin.tar.zst
    DIGEST=6dac7a8f9d6d0bc339b4ea9376c06a88f3fd1a7f462beb3c7ded9fbc934f3fb5
    ;;
  *)
    echo "UNSUPPORTED PLATFORM: $(uname -s)/$(uname -m)"
    echo "Recorded archives cover Linux x86_64/aarch64 and macOS arm64/x86_64 only."
    exit 1
    ;;
esac
# --- end platform selection -----------------------------------------------------------------
echo "platform $(uname -s)/$(uname -m): ${ASSET}"

# CI step 2 [Verify reports/PROOF.sha256]. The hash manifest.
python3 scripts/gen_proof_sha256.py --check

# CI step 3 [Import invariant]. On its own — not merely inside the gate at the end. CI runs
#            it here so a structural mistake fails in seconds instead of after an install and a
#            build, and so that the first failure a reader sees is the first failure CI reports.
python3 scripts/check_imports.py

# CI step 4 [Source policy]. Likewise on its own.
python3 scripts/check_source_policy.py

# CI step 5 [Cross-check lean-toolchain]. It must name the release this script installs.
#            Without this check, a
#            repointed lean-toolchain passes locally (the manifest was regenerated, so nothing
#            else notices) and fails in CI — a green local run against a red CI run, in exactly
#            the check this section exists for.
actual_pin="$(tr -d '[:space:]' < lean-toolchain)"
if [ "${actual_pin}" != "leanprover/lean4:v${EXPECTED_LEAN_VERSION}" ]; then
  echo "PIN MISMATCH: lean-toolchain says '${actual_pin}', this script installs v${EXPECTED_LEAN_VERSION}"
  exit 1
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

# CI step 6 [Install Lean from the pinned]. Fetch the archive by its versioned release URL and
#            compare the digest BEFORE
#            unpacking. The URL selects a release; the digest is what pins the bytes. `-c` exits
#            nonzero on a mismatch, and `set -e` stops the script here.
curl -fsSL --retry 3 -o "${WORK}/${ASSET}" \
  "https://github.com/leanprover/lean4/releases/download/v${EXPECTED_LEAN_VERSION}/${ASSET}"
( cd "${WORK}" && if command -v sha256sum >/dev/null 2>&1; then
    echo "${DIGEST}  ${ASSET}" | sha256sum -c -
  else
    echo "${DIGEST}  ${ASSET}" | shasum -a 256 -c -    # macOS, no GNU coreutils
  fi )

#            Only now unpack, and move the toolchain to the fixed directory, so that later
#            commands can name it explicitly instead of hoping PATH is right.
mkdir -p "${WORK}/unpacked"
tar --zstd -xf "${WORK}/${ASSET}" -C "${WORK}/unpacked"   # needs zstd; or: unzstd + tar -xf
FOUND="$(find "${WORK}/unpacked" -type f -path '*/bin/lean' -print -quit)"
if [ -z "${FOUND}" ]; then
  echo "INSTALL FAILED: no bin/lean in the unpacked archive"
  exit 1
fi
rm -rf "${PREFIX}"
mkdir -p "$(dirname "${PREFIX}")"
mv "$(dirname "$(dirname "${FOUND}")")" "${PREFIX}"
PATH="${PREFIX}/bin:${PATH}"
export PATH

# CI step 7 [Toolchain self-report]. CI checks the version and release commit here; locally
#            there is one more thing to check that CI gets for free from $GITHUB_PATH — that the
#            `lean` which actually resolves is the one just installed. Both guards exit 1.
if [ "$(command -v lean)" != "${PREFIX}/bin/lean" ]; then
  echo "WRONG LEAN ON PATH: $(command -v lean), expected ${PREFIX}/bin/lean"
  exit 1
fi
actual="$(lean --version)"
echo "lean --version: ${actual}"
case "${actual}" in
  *"version ${EXPECTED_LEAN_VERSION}"*"commit ${EXPECTED_LEAN_COMMIT}"*) ;;
  *)
    echo "TOOLCHAIN MISMATCH: expected version ${EXPECTED_LEAN_VERSION}, commit ${EXPECTED_LEAN_COMMIT}"
    echo "got: ${actual}"
    exit 1
    ;;
esac
lake --version

# CI steps 8-11 [lake build | Regression fixtures | Proof gate | Document claims].
#            Build, the fixtures, the gate, the document-claim check.
lake clean && time lake build
python3 scripts/regression_fixtures.py
./scripts/check_axioms.sh
python3 scripts/check_doc_claims.py

echo
echo "ALL CHECKS PASSED with the verified toolchain at ${PREFIX}"
```

The script exits 0 only if every step passed: the three toolchain-free checks, the pin
cross-check, the archive digest, the `lean` on `PATH` being the one just installed and reporting
the expected version and release commit, the cold build, 31 fixture runs covering 15 failure modes,
the three-layer proof gate, and the document-claim check.

**The equivalence claimed in this section is between the `lean` job of
`.github/workflows/ci.yml` and running this file** — not between CI and any subset of these lines
executed by hand. The numbered steps are CI's steps in CI's order: the manifest, the import
invariant and the source policy run *before* the toolchain is fetched, exactly as they do in the
workflow, so the first failure a reader sees locally is the first failure CI would report. An
earlier version of this section installed Lean first and never ran the import invariant or the
policy on their own — the outcome agreed on a healthy tree, the order and the first observable
failure did not.

To keep the toolchain for later shells, add `export PATH="$HOME/.local/lean-4.31.0/bin:$PATH"` to
your shell profile. The install path is fixed and version-named precisely so that "which `lean`
am I using" stays answerable at any later moment, rather than only inside one script's lifetime.


`lean-toolchain` still names `leanprover/lean4:v4.31.0` and is still the human-readable pin;
CI cross-checks its content against the version it installs and fails if the two have drifted, so
bumping one without the other is a build failure rather than a silent divergence.

### What the digest comparison establishes, and what it does not

**Establishes.** The bytes that are unpacked and run are exactly the bytes whose SHA-256 is
recorded above and in the workflow. Note which half of that does the work: the release URL is
*versioned*, not immutable — it names a tag and a filename, and GitHub permits both a tag to move
and a release asset to be replaced. What is immutable here is the recorded digest. The URL says
which file to ask for; the digest decides whether the answer is accepted. A corrupted or substituted download — including one served by
a compromised or intercepted connection — fails the digest comparison and never reaches unpacking
or the installed toolchain directory. Precisely: `curl` writes the archive into a throwaway
`mktemp -d` first, so a bad download does touch the disk; what it never reaches is `tar`, the
`$HOME/.local/lean-…` directory, or any execution, and the `trap` removes the temporary directory
on exit. If the
release asset were re-uploaded upstream (GitHub permits replacing a release asset; a tag is a
mutable ref and so, in practice, are the files hanging off it), the comparison would fail rather
than silently install different bytes.

**Does not establish — the host.** Every sentence above assumes the tools doing the checking are
telling the truth. They are not verified by anything here: `curl` fetches the archive,
`sha256sum` (or `shasum`) compares the digest, `tar` and `zstd` unpack it, `sh` sequences it,
`find` locates the binary, `python3` runs four of the five checks, and in CI the whole job runs on
`ubuntu-latest` — a moving image, rebuilt by GitHub, and unlike `actions/checkout` **not pinned by
digest**. On a compromised host, `sha256sum` can print `OK`, `lean --version` can print the
expected release commit, and every check can exit 0, without any of it being so. What the digest
genuinely rules out is a substituted or corrupted *download* on an honest host, which is the
realistic threat and the reason it is here. It cannot rule out a subverted host, and this document
does not claim to. See "Trust boundary" in `reports/PROOF.md`, which lists this alongside the
other things trusted unverified.

**Does not establish — upstream.** This is not an upstream attestation. `leanprover/lean4` publishes no
checksum file and no signature for the v4.31.0 release — the release body is a single link to the
release notes, and the asset list contains no `SHA256SUMS`, `.asc` or `.sig` entry. The digests
above are the values GitHub's release API reports for the stored assets
(`assets[].digest` on `https://api.github.com/repos/leanprover/lean4/releases/tags/v4.31.0`),
retrieved on 2026-09-09 and re-derivable with:

```sh
curl -fsSL https://api.github.com/repos/leanprover/lean4/releases/tags/v4.31.0 \
  | python3 -c 'import json,sys; [print(a["digest"], a["name"]) for a in json.load(sys.stdin)["assets"]]'
```

So what is bound here is "the bytes GitHub served for this release when these values were
recorded", checked on every download since. It is not a statement signed by the Lean developers,
and nothing in this repository can turn it into one. Nor does any of it say anything about the
*content* of that toolchain: the Lean binary and its kernel are trusted here, unverified, as they
are in every Lean development.

**`lean --version` is a diagnostic.** It is a string the freshly installed binary prints about
itself, which a substituted binary could print just as easily. It is still checked in CI, because
it catches a mismatch between the recorded digest and the recorded version — a bump that changed
one and forgot the other — but the archive digest, not this line, is what pins the toolchain.

**No cache, deliberately.** CI does not cache `~/.elan/toolchains` or the unpacked toolchain. A
cache restore copies bytes from a store other jobs can write to, and restoring one would bypass
the digest comparison that is the whole point. Re-downloading ~530 MB per run costs a few seconds
on a GitHub runner and keeps the property unconditional: every run verifies the archive it is
about to unpack. An earlier version of this workflow cached the toolchain and folded the expected
release commit into the cache key; that made a repointed tag unable to *serve* a stale entry, but
it still trusted whatever the cache returned.

**elan is not used.** `elan` is Lean's toolchain manager and the normal way to install Lean; it
reads `lean-toolchain` and fetches the named tag. It is not used here because it downloads and
unpacks the toolchain internally, leaving no point at which this repository can compare the
archive against a recorded digest before it is installed. Installing the archive directly costs
the convenience of `elan`'s toolchain switching, which a single-toolchain repository does not
need.

**Note on the record above.** The `lake` path in the table at the top of this file
(`/opt/homebrew/bin/lake`) is the Homebrew install that happened to be on the machine where the
timings were recorded. That is a record of what ran there, not a recommendation: the reproducible
path is the archive procedure in this section, which is what CI does.

No `opam`, no crate registry, no network access at build time beyond fetching the pinned Lean
toolchain itself. `lake-manifest.json` has an empty package list, so `lake build` never touches a
package registry.

## Reproduce the cold-build timing claim

```sh
lake clean && time lake build
```

Recorded here: `12 jobs`, real time in the low single-digit seconds (macOS, Apple M-series, warm
toolchain cache, cold `.lake/build`) — see `reports/PROOF.md`'s "Live run" for a full transcript
of one such run. The exact figure varies by machine and by filesystem cache state between runs
even on the same machine; it is illustrative, not a performance claim to reproduce byte-for-byte.
CI times this independently on `ubuntu-latest` on every run; see the `lean` job of
`.github/workflows/ci.yml`.
