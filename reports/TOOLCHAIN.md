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

**Run the script below as a script, not by pasting lines into a shell.** It is written with
`set -eu` and it *exits nonzero* on a digest mismatch and on a version or release-commit
mismatch — the same two failures that fail the `lean` job of `.github/workflows/ci.yml`, with the
same pinned URL, the same comparison and the same expected values. Read line by line and typed by
hand, it would print the same output and stop at nothing; the equivalence claimed here is between
CI and *running this file*, and it is why it is a file. An earlier version of this section
suggested piping an installer script from a mutable branch with no comparison at all.

Pick the archive for your platform:

| Platform | Archive (all under `https://github.com/leanprover/lean4/releases/download/v4.31.0/`) | SHA-256 |
|---|---|---|
| Linux x86-64 (what CI uses) | `lean-4.31.0-linux.tar.zst` | `07a633cc8d9151cbc08825ea4cdda50d4b02a2c9cb852c0131b13046f49cad7f` |
| Linux aarch64 | `lean-4.31.0-linux_aarch64.tar.zst` | `b1bf1d3c586b76cf4a86212a595d8b9edd99f438a41cce85d5780fa9347c811b` |
| macOS aarch64 (Apple silicon; the machine this file records) | `lean-4.31.0-darwin_aarch64.tar.zst` | `264105500c8abdf37b68ffe03390a783ed259807807222698da8dd92d6ce0a27` |
| macOS x86-64 | `lean-4.31.0-darwin.tar.zst` | `6dac7a8f9d6d0bc339b4ea9376c06a88f3fd1a7f462beb3c7ded9fbc934f3fb5` |

Save this as `install-lean.sh` and run it with `sh install-lean.sh`:

```sh
#!/bin/sh
# Installs the Lean toolchain this repository is pinned to, verifying the archive before it is
# unpacked and the toolchain before it is used. Exits nonzero at the first failure.
set -eu

# --- from the table above; change both together, never one alone ---------------------------
ASSET=lean-4.31.0-darwin_aarch64.tar.zst
DIGEST=264105500c8abdf37b68ffe03390a783ed259807807222698da8dd92d6ce0a27
EXPECTED_LEAN_VERSION=4.31.0
EXPECTED_LEAN_COMMIT=68218e876d2a38b1985b8590fff244a83c321783
PREFIX="$HOME/lean-toolchain-install"

# 1. Fetch the archive by its versioned release URL. The URL selects a release; the digest
#    below is what actually pins the bytes.
curl -fsSL --retry 3 -O "https://github.com/leanprover/lean4/releases/download/v${EXPECTED_LEAN_VERSION}/${ASSET}"

# 2. Compare the digest BEFORE unpacking. `-c` exits nonzero on a mismatch, and `set -e` stops
#    the script here.
if command -v sha256sum >/dev/null 2>&1; then
  echo "${DIGEST}  ${ASSET}" | sha256sum -c -
else
  echo "${DIGEST}  ${ASSET}" | shasum -a 256 -c -    # macOS, no GNU coreutils
fi

# 3. Unpack and put its bin/ on PATH.
mkdir -p "${PREFIX}"
tar --zstd -xf "${ASSET}" -C "${PREFIX}"             # needs zstd; or: unzstd + tar -xf
LEAN_BIN="$(dirname "$(find "${PREFIX}" -type f -path '*/bin/lean' -print -quit)")"
[ -n "${LEAN_BIN}" ] || { echo "INSTALL FAILED: no bin/lean in the unpacked archive"; exit 1; }
PATH="${LEAN_BIN}:${PATH}"
export PATH

# 4. Require the toolchain to report the version and release commit this repository expects.
#    This is the same comparison, with the same values, that CI performs — and it fails the
#    same way.
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

echo "toolchain verified; add ${LEAN_BIN} to PATH in your shell to build"
```

Only once that script has exited 0, and with `${LEAN_BIN}` on `PATH`:

```sh
cd ahl-proofs
lake clean && time lake build          # cold: 12 jobs, low single-digit seconds, exit 0
./scripts/check_axioms.sh              # three-layer proof gate, exit 0 on PASS
python3 scripts/regression_fixtures.py # the six regression fixtures, exit 0 when each still fails
```

`lean-toolchain` still names `leanprover/lean4:v4.31.0` and is still the human-readable pin;
CI cross-checks its content against the version it installs and fails if the two have drifted, so
bumping one without the other is a build failure rather than a silent divergence.

### What the digest comparison establishes, and what it does not

**Establishes.** The bytes that are unpacked and run are exactly the bytes whose SHA-256 is
recorded above and in the workflow. Note which half of that does the work: the release URL is
*versioned*, not immutable — it names a tag and a filename, and GitHub permits both a tag to move
and a release asset to be replaced. What is immutable here is the recorded digest. The URL says
which file to ask for; the digest decides whether the answer is accepted. A corrupted or substituted download — including one served by
a compromised or intercepted connection — fails step 2 and never reaches the filesystem. If the
release asset were re-uploaded upstream (GitHub permits replacing a release asset; a tag is a
mutable ref and so, in practice, are the files hanging off it), the comparison would fail rather
than silently install different bytes.

**Does not establish.** This is not an upstream attestation. `leanprover/lean4` publishes no
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
