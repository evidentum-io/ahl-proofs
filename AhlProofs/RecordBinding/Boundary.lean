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
a dataset id carrying `0x1F` or `0x7F`. That obligation is discharged by the conformance
corpus, and Lemma 1a is precisely the argument for why the two negative vectors
`dataset-id-control-octet-0x1f` and `dataset-id-control-octet-0x7f` must be in the v1.0
corpus: without the check the `WF` hypothesis fails, the first `0x1F` need no longer end
`dsid`, and two distinct triples share a preimage with no hash collision involved.

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

## Not proved: the relationship to the reference implementation

`ahl-core`'s `commit_plain`, `commit_keyed` and `descriptor::validate_dataset_id` are bound to
this model by the published conformance vectors, not by extraction or translation (invariants
page Section 5, planned I-D Section 8.7.6).
-/
