# ahl-proofs

Machine-checked proofs of the AHL invariants, in Lean 4. This repository currently contains
**Lemma 1, record binding** and **Lemma 2, revocation completeness relative to a checkpoint** —
the first two of the three lemmas listed on the AHL invariants page
(`ahl/docs-md/ahl-invariants.md`). Their sources in the protocol document are the AHL I-D
revision 0.4, Sections 2.6, 8.1 and 8.6 (Lemma 1) and Sections 2.4, 5.1 to 5.4, 7.2 and the
Section 7.5.1 erratum 4d (Lemma 2).

No `sorry`. No `axiom` declaration of our own: every assumption is a parameter or a structure
field carrying a doc comment that cites the I-D section it comes from.

## Build

```
lake build
```

Toolchain: `leanprover/lean4:v4.31.0`, pinned in `lean-toolchain`. **No Mathlib**, and no
other dependency. Lemma 1 needs only `List` facts Lean's own prelude provides
(`List.append_inj`, `List.cons.injEq`, `List.mem_cons_of_mem`). Lemma 2 needs finite-set
reasoning, which is where a library would normally be reached for; the two facts actually
required — that filtering by a strictly stronger predicate shortens a list, and duplicate
removal — are eleven and eight lines respectively (`length_filter_lt_of_witness`, `nub`), so
the dependency-free build is kept. A dependency-free build is faster to check and easier to
audit, so it stays that way for as long as the lemmas allow.

## Lemma 1 — the model (invariants page Section 0)

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

## Lemma 1 — assumptions

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
   `DescriptorModel.jcs_inj : Function.Injective JCS`. Lemma 1c consumes its contrapositive,
   `DescriptorModel.jcs_ne : D₁ ≠ D₂ → JCS D₁ ≠ JCS D₂`, derived in `Model.lean`. It is a
   parameter of the model, so every lemma that uses it says so in its own statement.

## Lemma 1 — record binding (invariants page Section 1)

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

## Lemma 2 — revocation completeness relative to a checkpoint

`AhlProofs/Closure/Model.lean`, `AhlProofs/Closure/RevocationCompleteness.lean`.

**No cryptographic assumption enters Lemma 2.** There is no hash, no signature and no
parameter to instantiate: the lemma is about a finite graph computation over the prefix a
checkpoint commits. Time does not appear either — an entry index is a list position
(«порядок = позиция», constitution article 9) and a trigger's scope is an abstract predicate on
an abstract valid-time type.

| Model | Lean |
| --- | --- |
| `RecordRef = (ds, r)` | `structure RecordRef` (`dataset`, `record`) |
| Statement kinds the closure reads | `inductive Statement` (`ingestion`, `derivation`, `retraction`, `correction`, `other`) |
| Log entry, with the erratum-4d void flag | `structure Entry` (`statement`, `void`) |
| Corpus under checkpoint `C`, `S_C` | `log.take treeSize` |
| `G_C` | `edges log treeSize` |
| `seeds(t)` | `trigger_seeds log t` |
| `lfp F_t` — reachability from the seeds, seeds included | `ClosureReach`, computed by `closure_reach` |
| `affected(t, C)` — the affected set, seeds excluded | `AffectedSet`; at a checkpoint, `Affected log treeSize t`, computed by `affected_at` |

**Seeds are not affected records.** `ClosureReach` is reachability from the seeds with the
seeds included — the least fixed point the traversal computes — and `AffectedSet` is that
closure *minus the seeds*, following I-D Section 5.1 as corrected on 2026-09-04 and `ahl-core`
("Seeds are never members of `Closure::affected`"). A seed is the record the trigger acts on
and the trigger itself dispositions it. Every clause below is stated about `AffectedSet`.

* **Lemma 2a — existence, uniqueness, termination.** `closureReach_isLeastClosed` says the
  closure is the least fixed point of the Section 5.1 operator: it contains the seeds, is
  closed under scope-covered edges, and is contained in every set with those two properties.
  `isLeastClosed_unique` says any two least fixed points coincide, so "the" closure — and with
  it the affected set — is well defined. `exists_stable`, `mem_closure_reach_iff` and
  `mem_affected_set_iff` give termination: the Kleene iteration from the seeds stabilises
  within `|RecordRef(G_C) ∪ seeds|` steps (the page's bound, amended 2026-09-04) and its result
  has exactly the members of the least fixed point. The stable stage is found by bounded search,
  so the proof is constructive: no clause of Lemma 2 depends on `Classical.choice`. Cycles are
  no obstacle — the iteration is over a set, not over paths (I-D Section 5.4, "MUST NOT loop").
* **Each record once.** `nodup_level`, `nodup_closure_reach`, `nodup_affected_set` and
  `nodup_affected_at`: every stage of the iteration and both computed sets are duplicate-free,
  which is what I-D Section 5.4 ("dispositions each record once") requires. A self-loop or two
  derivations producing one record cannot list it twice.
* **Lemma 2b — determinism, and decidability of disagreement.** `affected_of_prefix_eq`: two
  verifiers holding the same prefix `S_C` compute the same affected set. Order-freeness is
  built in — the specification is the inductive `ClosureReach`, and 2a says any least fixed
  point whatsoever equals it, so no traversal order can matter. The comparison against the
  anchored disposition list is not merely "decidable in principle": `dispositionsAgree` is a
  Boolean function of two finite lists — a duplicate check on the claim plus a bidirectional
  subset check — and `dispositionsAgree_iff` proves it equivalent to "the claim lists each
  affected record once and nothing else".
* **Lemma 2c — monotonicity in the checkpoint.** `affected_mono`: for `C' ⊒ C` the affected set
  at `C` is contained in the one at `C'`. A later checkpoint only adds edges (`edges_mono`), and
  the closure is monotone in the edge set (`closureReach_mono_edges`). The checkpoint must
  commit the trigger, which `Affected` carries as the conjunct `t < tree_size`
  (I-D Section 5.1); `C' ⊒ C` preserves it.
* **Lemma 2d — the seeding rules genuinely differ.** `seeding_rules_differ` and
  `affected_retraction_ne_correction` exhibit a corpus in which, with one and the same scope, a
  retraction on `X` and a correction of `X` have different affected sets: the correction seeds
  the superseded replacement `Xold` and reaches its consumer, the retraction does not. Section
  5.1 cannot be collapsed into one seeding rule. The witness is the shape of the corpus scenario
  `retraction-after-correction.json` and its contrast `supersession-chain.json`.

Void entries (I-D Section 7.5.1 erratum 4d, "never effective and never traversed") are part of
the model: `edgesOf_void`, `trigger_seeds_void`, `not_affected_of_void_trigger` and
`edges_cons_void` state that a void entry contributes no edge, no seed, and no affected record.

Nothing in Lemma 2 uses choice. `#print axioms` for every theorem in the two closure modules
shows at most `propext` and `Quot.sound`, so the decision procedure is an algorithm rather than
a classical existence claim.

## Boundary

`AhlProofs/RecordBinding/Boundary.lean` states what Lemma 1 does *not* prove: that `b` is the
correct canonicalization of the record; that any implementation actually validates the dataset
id; that a commitment does not disclose the record; and the collision-resistance assumption
itself.

`AhlProofs/Closure/Boundary.lean` states what Lemma 2 does *not* prove: completeness is
relative to the declared corpus and says nothing about derivations that were never anchored
(I-D Section 5.3); that the prefix a verifier holds is the log's true prefix is Lemma 3's
business, not Lemma 2's; nothing about publication completeness or split-view
(I-D Section 3.3); nothing about which entries are void or which triggers are authorized; and
nothing about time.

The invariants page requires a boundary for every lemma (AHL constitution, article 8).

## Relationship to the reference implementation

These are properties of the **model**, and of nothing else. There is no extraction, no
translation, and no refinement argument connecting `ahl-core` to the definitions here; the
names were aligned (`commit_plain`, `commit_keyed`, `DATASET_SEPARATOR`,
`descriptor::validate_dataset_id`) so a reader can hold the two side by side, which is a
convenience and not a proof.

What connects them today is **test evidence**: the conformance vector corpus of `ahl-core`
v0.3.0 (`test_data/`, at the crate's tagged revision) exercises the implementation on named
inputs and records what it does with them. For Lemma 2 the corresponding material is
`test_data/vectors/closure/` — six scenarios, among them `retraction-after-correction.json`
and `supersession-chain.json`, the pair the invariants page names as the witnesses for the
seeding distinction of Lemma 2d. For the `WF` hypothesis of Lemma 1a the witnesses
are the two negative vectors
`test_data/vectors/statements/malformed/dataset-id-control-octet-0x1f.json` and
`test_data/vectors/statements/malformed/dataset-id-control-octet-0x7f.json`, which drive
`descriptor::validate_dataset_id` with exactly the two octets I-D Section 2.6 singles out.
Lemma 1a is the argument for why those two vectors matter — remove the check and distinct
triples share a preimage with no hash collision involved.

That is engineering linkage, not a proved binding. A finite corpus cannot establish that every
path through an implementation validates `WF`, nor that its preimage construction refines
`AhlProofs.pre`; it establishes that the named inputs produce the named results at the named
revision. The word **bound** is reserved for a refinement argument, which does not exist yet.
Until one does, the Lean results and the corpus results are two separate bodies of evidence
about the same design — which is what invariants page Section 5 and the planned I-D
Section 8.7.6 should be read as saying.
