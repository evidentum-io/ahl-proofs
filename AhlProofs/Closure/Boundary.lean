import AhlProofs.Closure.RevocationCompleteness

/-!
# Lemma 2 — the boundary (what is NOT proved)

The AHL invariants page requires every lemma to name its boundary; a lemma without one is an
error (AHL constitution, article 8). This module carries no Lean content on purpose. The page's
«Граница» for Lemma 2 quotes I-D Section 5.3, and the items below are that boundary, each said
in terms of the definitions in `AhlProofs/Closure/RevocationCompleteness.lean`.

## Completeness is relative to the corpus, never absolute

`Affected log treeSize t` is computed from the entries the log carries below `treeSize`, and
says nothing about derivations that were never anchored. I-D Section 5.3: "What this does not
establish is that derivations outside the corpus do not exist. That is the manifest's coverage
assertion, auditable by comparing the declared inclusion and exclusion lists against the
organization's actual systems." That is an audit question, not a cryptographic one, and no
theorem here touches it.

## Lemma 2b assumes both verifiers hold the same prefix

`affected_of_prefix_eq` has `log₁.take n = log₂.take n` as a hypothesis. That the prefix a
verifier holds IS the log's true prefix `[0, n)` is not established by anything in this file —
it is what authenticated enumeration gives (I-D Section 3.1 item 5), i.e. Lemma 3. Without
Lemma 3, Lemma 2 is a statement about a computation, not about a corpus. Below L3 no
completeness is claimed at all (I-D Section 5.3), and this development claims none.

## Nothing about publication or split-view

A closure computed over a prefix says nothing about whether the checkpoint shown is the latest
published one, and nothing about a log presenting different views to different parties
(I-D Section 3.3). Those are the witness protocol's concern and are outside Lemma 2 exactly as
they are outside Lemma 3's statement.

## Nothing about void entries beyond their exclusion

`edgesOf_void`, `trigger_seeds_void` and `not_affected_of_void_trigger` say what a void entry
contributes: nothing. Whether a given entry IS void is decided by envelope verification
(I-D Section 7.5.1 erratum 4d), which this model does not perform — voidness is a flag on the
entry here. The same holds for a trigger's authority: an unauthorized but valid trigger is a
challenge and "is never traversed by closure" (I-D Section 2.4.3); this model does not decide
authority, so a trigger reaching `trigger_seeds` is assumed to be the effective one.

## Nothing about time

Scope filtering is an abstract predicate on an abstract valid-time type. That
`retroactive: false` really means "the derivation's `valid_time` intersects
`[effective_from, ∞)`" (I-D Section 2.4.3) is a property of the bitemporal comparison in
`ahl-core::bitemporal`, not of this model, which never interprets `V`.

## Relationship to the reference implementation

There is no extraction, no translation and no refinement argument connecting
`ahl-core/src/closure.rs` to these definitions. Names were aligned (`RecordRef`, `Edge`,
`edges`, `trigger_seeds`, `affected_set`) so the two can be read side by side, which is a
convenience for the reader and not a proof.

What connects them is test evidence: the closure scenarios of the conformance corpus at
`ahl-core` v0.3.0 — `test_data/vectors/closure/`, among them
`retraction-after-correction.json` and `supersession-chain.json`, the two the invariants page
names for Lemma 2d — record what the implementation computes on those named inputs. A finite
corpus cannot show that the implementation's traversal computes the least fixed point on every
input, nor that its edge extraction refines `AhlProofs.Closure.edges`. It shows that the named
scenarios produce the named affected sets at the named revision, and no more. The word "bound"
is reserved for a refinement argument, which does not exist yet.
-/
