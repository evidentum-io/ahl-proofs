# ahl-proofs

Machine-checked proofs of the AHL invariants, in Lean 4. This repository contains all three
lemmas of the AHL invariants page (`ahl/docs-md/ahl-invariants.md`): **Lemma 1, record
binding**, **Lemma 2, revocation completeness relative to a checkpoint**, and **Lemma 3,
append-only consistency**. Their sources in the protocol document are the AHL I-D revision 0.4
(which has no resolvable revision identifier yet — see "Immutable identifiers" in
`reports/PROOF.md`), Sections 2.6, 8.1 and 8.6 (Lemma 1); Sections 2.4, 5.1 to 5.4, 7.2 and the Section 7.5.1
erratum 4d (Lemma 2); and Sections 2.7, 3.1, 3.2, 7.4, 7.5 and 8.3 with RFC 9162 Section 2.1
(Lemma 3).

**Scope, up front:** every theorem here is a theorem about the Lean model in the three
`Model.lean` files, not about `ahl-core`/`atl-core`'s Rust code. There is no extraction and no
refinement proof connecting the two; the only link is a conformance-vector test corpus, which is
evidence, not a proof. See "What is NOT established" in `reports/PROOF.md` and "Relationship to
the reference implementation" below before citing this repository as covering the
implementation.

No unfinished proof. No `axiom` declaration of our own: every assumption is a parameter or a
structure field carrying a doc comment that cites the I-D section it comes from.
`./scripts/check_axioms.sh` checks both claims by machine on every CI run, over every constant in
the compiled `Lean.Environment` this repository produces — not a curated subset of theorems — and
`lake build` itself also fails on the `declaration uses 'sorry'` warning alone. Read
**"Trust boundary"** in `reports/PROOF.md` first: it states, in one place, what these checks
establish and the thing they cannot establish — they live in the repository they check, so they
are strong against forgetting and weak against intent. "Continuous integration and audit" below
describes the mechanism.

## Build

```
lake build
```

Toolchain: `leanprover/lean4:v4.31.0`, pinned in `lean-toolchain`. **No Mathlib**, and no
other dependency. Lemma 3 was the last chance for one — the RFC 9162 split point needs
`Nat.log2` and powers of two — and the prelude turned out to carry everything required
(`Nat.log2_self_le`, `Nat.lt_log2_self`, `Nat.two_pow_pos`, `Nat.pow_le_pow_right`), so the
dependency-free build stands for all three lemmas. Lemma 1 needs only `List` facts Lean's own
prelude provides
(`List.append_inj`, `List.cons.injEq`, `List.mem_cons_of_mem`). Lemma 2 needs finite-set
reasoning, which is where a library would normally be reached for; the two facts actually
required — that filtering by a strictly stronger predicate shortens a list, and duplicate
removal — are eleven and eight lines respectively (`length_filter_lt_of_witness`, `nub`), so
the dependency-free build is kept. A dependency-free build is faster to check and easier to
audit, so it stays that way for as long as the lemmas allow.

## Continuous integration and audit

`.github/workflows/ci.yml` runs on every push (any branch) and every pull request. It installs
Lean from the official release archive fetched by URL and **compared against a recorded SHA-256
before it is unpacked** — not from a mutable tag whose identity is taken on the word of the
binary it installs — then runs `lake build`, which fails on any Lean warning
(`declaration uses 'sorry'` foremost, via `leanOptions.warningAsError` in `lakefile.toml`), and
then the proof gate. `reports/TOOLCHAIN.md` carries a single runnable script that performs the
same steps in the same order as that workflow — the hash manifest, the import invariant and the
source policy before the toolchain is fetched, then the pin cross-check, the digest-verified
install, the toolchain self-report, the build, the fixtures, the gate and the document-claim
check — with each block labelled by the CI step it corresponds to. It also says exactly what the
digest comparison does and does not establish: GitHub publishes those digests; the Lean
developers publish no checksum file or signature for this release, and this repository says so
rather than implying an upstream attestation.

The gate is `./scripts/check_axioms.sh`, three layers in order:

1. **Lean-file coverage and the import invariant** (`scripts/check_imports.py`) — every `.lean`
   file anywhere in the tree must belong to a declared category: a library module (`AhlProofs.lean`
   or a file under `AhlProofs/`, which must in turn be reachable by imports from the root module)
   or a file named in that script's `DECLARED_AUXILIARY`. A library module nobody imports is never
   compiled, so it is never audited either, and both `lake build` and the audit exit 0 while
   ignoring it entirely; a `.lean` outside both categories — in the repository root, say — was
   invisible to every check there was. The rule enumerates categories rather than directories, so
   there is no next directory to forget.
2. **The policy over source text** (`scripts/check_source_policy.py`) — four lexemes are rejected
   in every `.lean` file in the working tree, with no allowlist of files or places. This is a
   policy over sources, deliberately not a semantic check: it decides nothing about meaning, and
   exists because each of those spellings is a way to leave the next layer with nothing to find —
   a placeholder proof inside an `example` never becomes a constant in the environment, and a
   declaration whose kernel typecheck was locally disabled has a clean axiom closure precisely
   because nothing was checked.
3. **The environment audit** (`scripts/Audit.lean`) — the semantic layer, and the one that
   establishes what the proofs depend on. It does not discover its targets by parsing source
   text. An earlier version did (`scripts/list_theorems.py` feeding
   `scripts/check_axiom_output.py`, by regex over the `.lean` files), and that approach had two
   proven blind spots: a visibility modifier before the keyword `axiom` (`private axiom foo :
   False` was invisible to a regex anchored on the bare keyword), and a string literal containing
   the two characters `/-` confusing the comment-stripper into deleting whatever declaration
   followed. `scripts/Audit.lean` instead `import AhlProofs`s the already-built library and walks
   the compiled `Lean.Environment` directly — every constant whose home module is under
   `AhlProofs.*` (currently 645; not only the 102 named `theorem`/`lemma` declarations
   `scripts/list_theorems.py` still counts, purely for the prose numbers in this document, with
   no role in the audit any more) — checking, via `Lean.collectAxioms`, that none is our own
   `axiom`, that none has an axiom outside `{propext, Classical.choice, Quot.sound}` in its
   transitive closure (which is also how an unfinished proof is caught: it elaborates to the
   axiom `sorryAx`, so no text search for the word is needed), and that the set of constants
   whose closure contains `Classical.choice` is *exactly*
   `{commit_plain_descriptor_collision}` — the claim `ahl/docs-md/priority-zero.md` makes,
   checked here against every constant on every run, at a finer grain than the 102 named
   theorems, and it still holds exactly.

**15 fixture runs covering 9 failure modes** — an unimported module, an `example` under a locally
relaxed `warningAsError`, a locally skipped kernel typecheck, an unfinished theorem, a top-level
`axiom`, a new file left out of the hash manifest (run twice, with and without its `import` line,
to show the manifest layer works independently of the import invariant), a forbidden lexeme in the
sources (once per lexeme, so that no policy rule is left without a test), and audit tooling in a
subdirectory of `scripts/` (so that the manifest's promise to cover *every* audit script is
exercised, not merely intended) — are **run in CI on every push and pull request** by `scripts/regression_fixtures.py`, immediately before the gate.
Each is applied to a throwaway copy of the repository, and the runner asserts not only that the
pipeline exits nonzero but that the layer responsible is the one that failed, *and* that
`./scripts/check_axioms.sh` itself fails with the diagnostic naming that layer — so a wrapper that
stopped propagating an exit status is caught too. It also validates its own roster before
starting, so a truncated or emptied fixture list fails instead of reporting success over nothing.
The working tree is never written to, and the runner hashes every file under it except `.git/`,
`.lake/` and `__pycache__/` before and after to prove it. `reports/PROOF.md`, "Required regression
tests", lists all 15 runs with the exit status of every stage.

A defined list of claims in this file, in `reports/PROOF.md` and in `reports/TOOLCHAIN.md` is
itself checked in CI by `scripts/check_doc_claims.py`: four published transcripts, the counts, the
toolchain pin and all four release-archive digests, the fixture roster, and the install script
`reports/TOOLCHAIN.md` publishes — which must be a single block that passes `sh -n`, whose
`# CI step N [key].` labels must cover the workflow's steps once each, in order, whose commands
must match those of the steps they mirror (over a declared vocabulary, not full shell
equivalence), and whose platform-selection block is parsed — never executed — to confirm it picks
each recorded platform's archive and digest and refuses an unrecorded platform. `.github/workflows/ci.yml` is
the source of truth for the step order and is read structurally, by a dependency-free reader that
rejects anything outside the shape it understands rather than guessing. That list is
enumerated exhaustively under "What is checked about this document" in `reports/PROOF.md`, and
everything outside it — the mathematics, the section references, the build timings, the arguments
— is maintained by hand and is not machine-checked.

`reports/PROOF.md` states what the three lemmas prove and — the part that matters most for anyone
citing this repository — what they do **not**: there is no correspondence proof between this Lean
model and the `ahl-core`/`atl-core` Rust code, only the test-corpus linkage described under
"Relationship to the reference implementation" below. It also carries the **trust boundary** and
the **immutable identifiers** of everything this model was compared against.
`reports/TOOLCHAIN.md` records the toolchain pin and install procedure; `reports/PROOF.sha256`
(`scripts/gen_proof_sha256.py --check` in CI, which also hashes the workflow file itself) is a
same-commit internal-consistency check over every file that participates in the build or the
audit tooling — not a proof of integrity or provenance, since it is generated and committed by
the same process that could edit any of the files it covers — regenerated from a file *glob*
rather than a hand-maintained list, so a new `.lean` file cannot go unaudited without CI noticing
the manifest is stale.

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

## Lemma 3 — append-only consistency

`AhlProofs/Tree/Model.lean`, `AhlProofs/Tree/AppendOnly.lean`.

The tree model is RFC 9162 Section 2.1 geometry with the I-D Section 2.7 domain separation, over
the same abstract hash as Lemma 1: `M.H` is a parameter, nothing is assumed about it, and every
clause concludes the intended property **or an exhibited collision**.

| Model | Lean |
| --- | --- |
| Leaf hash `H(0x00 ‖ leaf)` | `leafHash` (`ahl-core` `leaf_hash`) |
| Node hash `H(0x01 ‖ L ‖ R)` | `nodeHash` (`atl_core` `hash_children`) |
| Largest power of two `< n` | `splitPoint` (`atl_core` `largest_power_of_2_less_than`) |
| `MTH` over leaf hashes | `MTHh` (`atl_core` `compute_root`) |
| `MTH` over entries | `MTH` (`ahl-core` `tree_root`) |
| `Incl(leaf, i, n, root, π)` | `verifyInclusion` (`ahl-core` `verify_inclusion_proof`) |
| `Consistent(m, n, r_m, r_n, π)` | `verifyConsistency` (`ahl-core` `verify_consistency_proof`) |
| `Range(i, j, n, root, E, π)` | `verifyRange` (`ahl-core` `range_proof::verify`) |

The engine of all three clauses is `mth_inj_or_collision`: two entry lists of the same length
with the same `MTH` are the same list, or a collision of `H` has been exhibited. Its proof is
the RFC 9162 recursion, using the same fixed-width append argument Lemma 1a uses to split a
node preimage back into its two 32-octet children.

* **Lemma 3a — consistency soundness.** `consistency_sound`: a verifying RFC 9162 consistency
  proof from `(m, MTH(L_m))` to `(n, MTH(L_n))` shows `L_m = L_n.take m` — append-only *within
  the view shown to the verifier* (I-D Section 8.3) — or exhibits a collision. The `m > k`
  branch of the RFC recursion is well formed because a prefix reaching past the split has the
  same split point (`splitPoint_eq_of_gt`, proved from `n ≤ 2 * splitPoint n`).
* **Lemma 3b — inclusion soundness.** `inclusion_sound`: a verifying inclusion proof for `leaf`
  at index `i` against `MTH(L)` shows `L[i]? = some leaf`, or exhibits a collision.
* **Lemma 3c — enumeration soundness.** `range_sound`: a verifying authenticated range proof
  over `[from, to)` shows the carried entries are the log's entries at those indexes, in order
  (`E = (L.take to).drop from`), or exhibits a collision. This is what makes the corpus `S_C` of
  Lemma 2 a complete prefix — "know that nothing was skipped" (I-D Section 3.1 item 5).
* **Lemma 3d — the composition of Lemmas 2 and 3.** `affected_mono_of_consistency`: a verifying
  consistency proof supplies exactly the hypothesis Lemma 2c needs, so `affected(t, C)` is
  contained in `affected(t, C')`. `enumerated_closure_eq`: an authenticated enumeration of the
  whole committed prefix carries the log's own entries, so the closure computed from the
  enumeration is the closure over the log's true prefix. Both take the entry decoder
  `decode : Bytes → Entry V` as a parameter — neither model parses an envelope — and hold for
  any decoder.

Three `example`s pin the verifier's shape: it accepts the empty path for a one-leaf tree and the
sibling leaf hash for a two-leaf tree, and it **rejects an out-of-range index** — `i < n` is a
conjunct of `verifyInclusion`, as RFC 9162 Section 2.1.3.2 requires ("if `leaf_index` is greater
than or equal to `tree_size`, stop"). Without it the empty path would open a one-leaf tree's root
at every index, 42 included.

**Where the modelled verifiers differ from the crate, deliberately.** `verifyConsistency` accepts
`m = n` (with an empty proof, requiring equal roots) where RFC 9162 Section 2.1.4 specifies
`0 < first < second`: the invariants page states Lemma 3a for `0 < m ≤ n` and the page is
followed, since Lemma 3d inherits `m ≤ n` from Lemma 2c. `verifyRange` formalises the
recomputation and the counting conditions of `range_proof::verify`, and omits three things
without claiming any of them redundant — the width-one cross-check through `atl-core`'s inclusion
verifier, the `AHLRP1` serialization, and the crate's saturating `u64` arithmetic (`Nat` cannot
overflow). Both are spelled out in the definitions' doc comments and in the boundary file.

**Choice-free.** `#print axioms` for every theorem of Lemma 3 shows at most `propext` and
`Quot.sound`. Two prelude lemmas used in the proofs (`List.take_add`, `List.drop_take`) carry
`Classical.choice` in their own footprint, so they are reproved by induction as `take_add'` and
`drop_take'`; and `omega` closing a non-arithmetic goal takes a classical `exfalso` path, so
those calls are written `False.elim (by omega)` instead.

## Boundary

`AhlProofs/RecordBinding/Boundary.lean` states what Lemma 1 does *not* prove: that `b` is the
correct canonicalization of the record; that any implementation actually validates the dataset
id; that a commitment does not disclose the record; and the collision-resistance assumption
itself.

`AhlProofs/Tree/Boundary.lean` states what Lemma 3 does *not* prove: it is about the view shown
to the verifier and detects no split-view (I-D Section 3.3); it says nothing about whether the
checkpoint shown is the latest published one, nothing about the checkpoint's signature or the
log's keys (I-D Section 8.3), and nothing about the *completeness* of the RFC 9162 proof
systems — only their soundness; the leaf construction and the parsing of entries are outside
the model.

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
v0.3.1 — commit `4c30994df5d37548428785b3615b496800cd31cb`, `test_data/` at that commit —
exercises the implementation on named inputs and records what it does with them. For Lemma 3 it is `test_data/vectors/merkle/` (`log-tree.json`, `batch-tree.json`,
`input-set-tree.json`, `range-proof.json` among them), `test_data/vectors/checkpoints/` and the
receipt vectors. Lemma 3 is a property of the **abstract model** in `AhlProofs/Tree/Model.lean`:
the model follows RFC 9162 Section 2.1, the I-D Section 2.7 prefixes and the range-proof
construction of `ahl-core/src/range_proof.rs` **by construction** — a modelling decision taken by
reading those documents and that code, not a theorem — and neither `ahl-core` nor `atl-core`
(commit `79ac9c08585720cbd0de79a31662d99f68efb2f0`, the revision `ahl-core@4c30994` pins, to
which `ahl-core` normatively delegates inclusion and consistency verification) is verified here.
For Lemma 2 the corresponding material is
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
revision — the named revision being the commit SHAs above, which is what "Immutable identifiers"
in `reports/PROOF.md` tabulates for all three artefacts. The word **bound** is reserved for a
refinement argument, which does not exist yet.
Until one does, the Lean results and the corpus results are two separate bodies of evidence
about the same design — which is what invariants page Section 5 and the planned I-D
Section 8.7.6 should be read as saying.

## License

Apache-2.0
