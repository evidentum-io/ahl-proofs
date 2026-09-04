# ahl-proofs

Machine-checked proofs of the AHL invariants, in Lean 4. This repository currently contains
**Lemma 1, record binding** — the first of the three lemmas listed on the AHL invariants page
(`ahl/docs-md/ahl-invariants.md`), whose source in the protocol document is the AHL I-D
revision 0.4, Sections 2.6, 8.1 and 8.6.

No `sorry`. No `axiom` declaration of our own: every assumption is a parameter or a structure
field carrying a doc comment that cites the I-D section it comes from.

## Build

```
lake build
```

Toolchain: `leanprover/lean4:v4.31.0`, pinned in `lean-toolchain`. **No Mathlib**, and no
other dependency — Lemma 1 needs only `List` facts that Lean's own prelude already provides
(`List.append_inj`, `List.cons.injEq`, `List.mem_cons_of_mem`). A dependency-free build is
faster to check and easier to audit, so it is kept that way for as long as the lemmas allow.

## The model (invariants page Section 0)

`AhlProofs/Model.lean`.

| Model | Lean |
| --- | --- |
| Octet strings | `Bytes := List UInt8` |
| Digest, exactly 32 octets | `structure Digest` (`octets`, `length_eq`) |
| Separator `0x1F` | `SEP` |
| Dataset id well-formedness | `WF` — 1..128 octets, each in `0x21..0x7E` |
| Commitment preimage | `pre dsid ddig b = dsid ++ 0x1F :: ddig.octets ++ 0x1F :: b` |
| Hash and keyed hash | `HashModel.H`, `HashModel.HMAC` |
| `plain` / `keyed` commitment | `HashModel.commit_plain`, `HashModel.commit_keyed` |
| Descriptor canonicalization | `DescriptorModel.JCS`, `HashModel.ddig` |
| An exhibited collision | `Collision f a b := a ≠ b ∧ f a = f b` |

The model knows nothing about JSON and nothing about the wire format. Names follow
`ahl-core/src/lib.rs` (`commit_plain`, `commit_keyed`, `DATASET_SEPARATOR`,
`descriptor::validate_dataset_id`) so the two can be read side by side.

## Assumptions

1. **CR — collision resistance of SHA-256** (I-D Section 8.1). *Not* a hypothesis anywhere in
   this development, and deliberately so. Injectivity of `H` would be false; instead the
   lemmas **conclude** `Collision H a b`, an exhibited pair. The assumption is the informal
   claim that such a pair cannot feasibly be produced — a statement about adversaries, which
   this model does not describe. `HashModel` assumes nothing whatever about `H`.
2. **CR of HMAC-SHA-256 under a known dataset key** (I-D Section 2.6). Same treatment:
   `commit_keyed_collision` concludes a collision of `HMAC k`. The I-D's reduction of that to
   SHA-256 by the RFC 6234 nesting is cited, not formalized.
3. **JCS-INJ — injectivity of RFC 8785 canonicalization on I-JSON values** (invariants page
   Section 0; I-D Section 2.6). The one assumption that *is* a hypothesis, as the field
   `DescriptorModel.jcs_inj : ∀ D₁ D₂, D₁ ≠ D₂ → JCS D₁ ≠ JCS D₂`. It is a parameter of the
   model, so every lemma that uses it says so in its own statement.

## The lemmas (invariants page Section 1)

`AhlProofs/RecordBinding.lean`.

* **Lemma 1a — `preimage_injective`**, unconditional. If two dataset ids are well-formed and
  the two commitment preimages are equal, the triples `(dsid, ddig, canonical bytes)` are
  equal. The proof is constructive and uses no cryptography: because a well-formed dataset id
  contains no `0x1F`, the first `0x1F` in the preimage ends `dsid`; `ddig` is then exactly 32
  octets; the octet after it is the second `0x1F`; the remainder is the canonical bytes. This
  is the I-D's "by parsing alone" (Section 2.6), and the parsing step is isolated as
  `split_at_first_sep`.

* **Lemma 1b — `commit_plain_collision`, `commit_keyed_collision`**. If two *distinct*
  well-formed triples receive the *same* commitment, then the two preimages are a collision of
  `H` (respectively of `HMAC k`). Read against assumption 1: the situation cannot feasibly
  arise, and an observer who sees it holds the witness.

* **Lemma 1c — `descriptor_digest_collision`, `commit_plain_descriptor_collision`**. The step
  the I-D marks as *not* unconditional. Distinct descriptors sharing a descriptor digest are a
  collision of `H` on their canonical encodings, under JCS-INJ. Composed with 1b: an equal
  `plain` commitment over distinct `(dataset id, descriptor, canonical bytes)` triples yields
  a collision of `H` — on the descriptor encodings or on the preimages.

A non-vacuity check at the end of the file exhibits a well-formed dataset id, so Lemma 1a's
hypothesis is not empty.

## Boundary

`AhlProofs/RecordBinding/Boundary.lean` states what is *not* proved: that `b` is the correct
canonicalization of the record; that any implementation actually validates the dataset id;
that a commitment does not disclose the record; and the collision-resistance assumption
itself. The invariants page requires a boundary for every lemma (AHL constitution, article 8).

## Relationship to the reference implementation

These are properties of the **model**. The reference implementation (`ahl-core`) is bound to
the verified model by the **published conformance vector corpus, not by extraction** — this is
the sentence planned for I-D Section 8.7.6 (invariants page Section 5). Lemma 1a is in
particular the argument for why the negative vectors `dataset-id-control-octet-0x1f` and
`dataset-id-control-octet-0x7f` are mandatory in the v1.0 corpus: they are what discharges the
`WF` hypothesis on the implementation side.
