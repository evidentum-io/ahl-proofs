import AhlProofs.RecordBinding

/-!
# Lemma 1 — the boundary (what is NOT proved)

The AHL invariants page requires every lemma to name its boundary; a lemma without one is an
error (AHL constitution, article 8). This module carries no Lean content on purpose: its
subject is the set of claims the record-binding lemmas do *not* make. Stating them here keeps
them next to the proofs instead of in a document that can drift away from them.

## Not proved: that `b` is the right canonicalization of the record

`AhlProofs.pre` takes the canonical bytes `b` as given. Whether those bytes are what the
dataset's canonicalization descriptor actually prescribes is a property of the descriptor
procedure (I-D Section 2.6, rule 2 and the `jcs` / `exact-bytes` identifiers), which lives
outside this model. A verifier that applies the wrong procedure computes a commitment over
different bytes; the lemmas say nothing about whether it should have.

## Not proved: that an implementation validates the dataset id

Lemma 1a assumes `WF dsid`. It does not — cannot — establish that any implementation rejects
a dataset id carrying `0x1F` or `0x7F`. What Lemma 1a supplies is the reason the check matters:
without it the `WF` hypothesis fails, the first `0x1F` need no longer end `dsid`, and two
distinct triples share a preimage with no hash collision involved.

The evidence that the reference implementation performs the check is empirical, and stays
empirical. In `ahl-core` v0.3.1 the two negative vectors
`test_data/vectors/statements/malformed/dataset-id-control-octet-0x1f.json` and
`…-0x7f.json` are the witnesses: they exercise `descriptor::validate_dataset_id` on exactly
the two octets Section 2.6 calls out. A finite corpus of test vectors cannot show that every
path through an implementation validates `WF`, nor that its preimage construction refines
`AhlProofs.pre`. It shows that the named inputs are rejected at the named revision, and no
more. The word "bound" is reserved here for a refinement argument, which does not exist yet.

## Not proved: anything about disclosure

A commitment does not reveal the record. That is a property of `H`, not of the encoding, and
the I-D states it as detection rather than disclosure (Section 8.6). `AhlProofs.HashModel`
assumes nothing at all about `H`, so no confidentiality claim can be — or is — derived here.

## Not proved: the collision-resistance assumption itself

Lemmas 1b and 1c conclude `AhlProofs.Collision`. That a collision cannot feasibly be produced
is the assumption of I-D Section 8.1, a statement about adversaries; it is not expressible as
a hypothesis over the functions of this model and is not asserted anywhere in this
development. Likewise the reduction of HMAC-SHA-256 collision resistance to that of SHA-256
(I-D Section 2.6, RFC 6234 nesting) is cited, not formalized: `commit_keyed_collision`
concludes a collision of `HMAC k` itself.

## Not proved: any relationship to the reference implementation

Nothing here says anything about `ahl-core`'s `commit_plain`, `commit_keyed` or
`descriptor::validate_dataset_id`. There is no extraction, no translation, and no refinement
argument connecting the Rust code to this model; the names were aligned so the two can be read
side by side, which is a convenience for a human reader and not a proof. The published
conformance corpus (`ahl-core` v0.3.1, `test_data/`) is test evidence that the implementation
behaves as the model does on the inputs the corpus names — engineering linkage, not a proved
binding. Closing that gap needs a refinement argument; until one exists, the model results and
the implementation results are two separate bodies of evidence about the same design
(invariants page Section 5, planned I-D Section 8.7.6).
-/
