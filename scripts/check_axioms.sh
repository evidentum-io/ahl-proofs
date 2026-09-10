#!/usr/bin/env bash
# The proof gate — three layers, run in order; any one of them failing fails the whole script.
#
#   1. scripts/check_imports.py        import invariant: every AhlProofs/**/*.lean in the working
#                                      tree is reachable by imports from AhlProofs.lean, so
#                                      everything present is built and therefore reaches layer 3.
#                                      Without it, a file nobody imports is neither compiled nor
#                                      audited, and both `lake build` and layer 3 exit 0.
#   2. scripts/check_source_policy.py  policy over source text: four lexemes with no legitimate
#                                      use here (Lean's two placeholder proof terms,
#                                      `warningAsError false`, `debug.skipKernelTC`) are rejected
#                                      in every .lean file. This is *not* a semantic check and
#                                      does not replace layer 3; it covers the two ways to keep
#                                      layer 3 quiet — a placeholder proof inside an `example`,
#                                      which never becomes a constant, and a locally disabled
#                                      kernel typecheck, whose axiom closure is clean because
#                                      nothing was checked.
#   3. scripts/Audit.lean              the semantic check: imports the already-built AhlProofs
#                                      library and walks the compiled `Lean.Environment`
#                                      (`env.constants`) via `Lean.collectAxioms` — every `def`,
#                                      `instance`, `private` declaration and generated helper
#                                      included, not only `theorem`/`lemma`. It checks: no axiom
#                                      of our own; no axiom outside
#                                      {propext, Classical.choice, Quot.sound} in any constant's
#                                      transitive closure (which is how a placeholder proof is
#                                      caught, as the axiom `sorryAx`, with no text search); and
#                                      the `priority-zero.md` claim that `Classical.choice` is
#                                      used by exactly one constant.
#
# Layers 1 and 2 read the working tree and need no build. Layer 3 assumes `lake build` has
# already produced up-to-date `.olean`s (CI runs the build as its own prior step; see
# .github/workflows/ci.yml) — it does not rebuild anything itself.
#
# That these three layers still work is itself tested: scripts/regression_fixtures.py applies 8
# known ways of breaking this repository, in 12 fixture runs, to throwaway copies of it and
# requires each to fail at the layer that owns it -- and requires THIS script, run on the same
# corrupted copy, to exit nonzero with the diagnostic naming that layer, so a wrapper that
# swallowed an exit status would be caught. CI runs it immediately before this script.
#
# What none of this defends against: a participant with write access editing these checks
# themselves. See "Trust boundary" in reports/PROOF.md, stated there rather than implied here.
#
# Exit code is nonzero on any failure. On success the last line is "extra axioms: (none) PASS",
# matching the audit convention used in dzatona/cose-parse-nopanic.

set -uo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

fail=0

echo "== layer 1/3: scripts/check_imports.py (import invariant) =="
python3 scripts/check_imports.py
status=$?
if [ "$status" -ne 0 ]; then
  echo "GATE FAILED - scripts/check_imports.py exited $status"
  fail=1
fi
echo

echo "== layer 2/3: scripts/check_source_policy.py (policy over source text) =="
python3 scripts/check_source_policy.py
status=$?
if [ "$status" -ne 0 ]; then
  echo "GATE FAILED - scripts/check_source_policy.py exited $status"
  fail=1
fi
echo

if [ "$fail" -ne 0 ]; then
  echo "GATE FAILED - refusing to run the environment audit on a tree that already fails a"
  echo "structural check: its result would describe a different tree than the one on disk."
  exit 1
fi

echo "== layer 3/3: scripts/Audit.lean (environment-based axiom & placeholder-proof audit) =="
lake env lean scripts/Audit.lean
status=$?
echo

if [ "$status" -ne 0 ]; then
  echo "AUDIT FAILED - lake env lean scripts/Audit.lean exited $status"
  exit 1
fi

exit 0
