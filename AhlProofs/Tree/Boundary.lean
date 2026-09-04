import AhlProofs.Tree.AppendOnly

/-!
# Lemma 3 — the boundary (what is NOT proved)

The AHL invariants page requires every lemma to name its boundary; a lemma without one is an
error (AHL constitution, article 8). The page's «Граница» for Lemma 3 quotes I-D Section 8.3
verbatim, and the items below are that boundary, said in terms of the definitions in
`AhlProofs/Tree/AppendOnly.lean`.

## Only the view shown to the verifier

Every clause is about the roots and proofs a verifier was handed. `consistency_sound` says that
the two roots stand in a prefix relation; it does not say that either root is the log's. A log
operator presenting **inconsistent views to different parties** — split-view — is not detected
by inclusion or consistency proofs at all (I-D Section 3.3), and is the witness protocol's
business, outside the lemmas.

## Not proved: that the checkpoint shown is the latest published one

Nothing here establishes that the checkpoint a verifier holds is the head of publication. The
page records this as an open question (`ahl-roadmap.md`) and a declared limitation in v1.0.

## Not proved: anything about the checkpoint's signature or the log's keys

`MTH`, `verifyInclusion`, `verifyConsistency` and `verifyRange` are statements about tree
structure. That the root came from a checkpoint signed by a key the manifest enumerates is
governance (I-D Sections 2.4.6, 7.5.1), not tree structure; log-key compromise is explicitly
outside Lemma 3 (I-D Section 8.3, last paragraph).

## Not proved: completeness of the RFC 9162 proof systems

Only **soundness** is proved: a proof that verifies implies the property, or exhibits a
collision. The converse — that the honest prover can always produce a proof that verifies,
i.e. that `inclusion_proof`, `consistency_proof` and `range_proof::generate` always succeed on
well-formed input — is not proved here. Completeness is what the conformance vectors exercise;
soundness is what a verifier's safety rests on.

## Not proved: collision resistance

As in Lemma 1, the conclusions are `… ∨ ∃ x y, Collision M.H x y`. That such a pair cannot
feasibly be produced is the assumption of I-D Section 8.1, a statement about adversaries; it
is not expressible over the functions of this model and is asserted nowhere. `HashModel`
assumes nothing whatever about `H`, so the results hold for any function of that type.

## Not proved: the leaf construction, or what a leaf means

`MTH` takes the entries as given octet strings. Which octets an AHL log entry contributes —
the adaptor profile's log-leaf construction of `ahl-core`'s `log_leaf`, JCS or the ATL-shaped
preimage — is outside the model, as is any parsing of those octets back into a statement. The
composition lemmas take that decoding as a parameter (`decode : Bytes → Entry V`) precisely
because neither model performs it.

## Not proved: the tree-building rules of I-D Section 2.7 beyond the geometry

Leaf ordering ("sorted by `record`") and the prohibition on duplicate leaves are manifest and
producer duties checked elsewhere; `MTH` hashes the list it is given, in the order it is given.

## Not proved: the accepted set of the modelled range verifier is the crate's

`verifyRange` formalises the recomputation of `range_proof.rs` together with its counting
conditions: a non-empty sub-range of `[0, n)`, exactly `to - from` carried entries, every carried
subtree hash consumed, and the recomputation opening the root. Three things in the crate's
`verify` have no counterpart here, and **no claim of redundancy is made for any of them**: the
width-one cross-check through `atl_core`'s inclusion verifier (an anti-drift guard), the
`AHLRP1` serialization, and the crate's saturating `u64` arithmetic. See the doc comment on
`AhlProofs.Tree.verifyRange`.

## A deliberate widening: `m = n` in the consistency verifier

RFC 9162 Section 2.1.4 specifies a consistency proof for `0 < first < second`; the invariants
page states Lemma 3a for `0 < m ≤ n`, and the page is what is followed. `verifyConsistency`
therefore accepts `m = n` with an empty proof list, in which case it requires the two roots to
be equal, and `consistency_sound` proves the prefix property for that case like any other. The
widening is documented rather than removed because Lemma 3d inherits `m ≤ n` from Lemma 2c,
whose monotonicity is stated for `n ≤ n'` including equality. A verifier wanting RFC-strict
behaviour adds `m < n`; nothing here depends on the wider domain.

## Relationship to the reference implementation

Lemma 3 is a property of the **abstract model in `AhlProofs/Tree/Model.lean`** — of `MTH`,
`verifyInclusion`, `verifyConsistency` and `verifyRange` as defined there. The model follows RFC
9162 Section 2.1 and the I-D Section 2.7 prefixes by construction, and its range proof follows
the construction `ahl-core/src/range_proof.rs` implements for the adaptor profile
`ahl-test-log-v1`; that correspondence was established by reading those documents and that code,
which is a modelling decision and not a theorem.

There is no extraction, no translation and no refinement argument connecting any crate to these
definitions — not `ahl-core`, and not `atl-core`, to which `ahl-core` normatively delegates
inclusion and consistency verification (the "anti-drift" rule in `ahl-core/src/lib.rs`) and which
this development likewise does not verify. Names were aligned (`leaf_hash`, `tree_root`,
`verify_inclusion_proof`, `verify_consistency_proof`, `range_proof::verify`) so the two can be
read side by side, which is a convenience for the reader and not a proof.

What connects them is empirical evidence: the conformance corpus at `ahl-core` v0.3.1 —
`test_data/vectors/merkle/` (among them `log-tree.json`, `batch-tree.json`,
`input-set-tree.json` and `range-proof.json`), `test_data/vectors/checkpoints/` and the receipt
vectors — records what the implementations compute on named inputs. A finite corpus cannot show
that either crate's verifier is sound on every input, nor that its proof serialization refines
the path and node lists here. It shows that the named inputs produce the named results at the
named revision, and no more. The word "bound" is reserved for a refinement argument, which does
not exist yet. This is the sense in which the invariants page directs Section 8 to speak of the
reference implementation and the published vector corpus.
-/
