# PROOF — the three AHL invariant lemmas

Machine-checked in Lean 4, no `sorry`, no `axiom` declaration of our own. This file states what
is proved, over what model, and — the part that matters most for anyone citing this repository —
what is **not** established. See `README.md` for the full mathematical account; this file is the
audit trail: exact theorem names, exact axiom dependencies, exact commands to reproduce both.

## Trust boundary

Read this before the results, not after.

Four checks stand between the **sources** of this repository and the **pipeline** that reports on
them. They do not stand between the sources and this document: `reports/PROOF.sha256` deliberately
does not hash the prose files, and prose is not something a build can validate. A fifth check
closes as much of that gap as can honestly be closed by machine — see "What is checked about this
document" below. The four:

* **The environment audit** — `scripts/Audit.lean`. It enumerates the constants of the
  *compiled* library (every `def`, `instance`, `private` declaration and generated helper, not a
  curated list of theorems) and computes each one's transitive axiom closure with
  `Lean.collectAxioms`. This is the check that establishes what the proofs actually depend on.
  Everything in "Axiom audit" below is its output.
* **The policy over source text** — `scripts/check_source_policy.py`. It rejects four lexemes in
  every `.lean` file in the working tree: Lean's two placeholder proof terms, `warningAsError`
  set to false, and `debug.skipKernelTC`. It decides nothing about meaning. It forbids spellings
  that have no legitimate use in this repository, each of which is a way to leave the environment
  audit with nothing to find — a placeholder inside an `example` never becomes a constant, and a
  declaration whose kernel typecheck was locally disabled has a clean axiom closure precisely
  because nothing was checked. It is a layer on top of the environment audit and never a
  substitute for it.
* **The regression fixtures** — `scripts/regression_fixtures.py`. 7 fixture runs covering 6
  failure modes of this repository, each applied to a throwaway copy of it, each required to fail
  *and* to fail at the layer that owns it. This is what keeps the other three honest: a layer that stopped working
  would turn a fixture green, and a green fixture is a red CI run. It is run in CI immediately
  before the gate, so the gate has to pass on the same tree afterwards. See "Required regression
  tests".
* **The import invariant** — `scripts/check_imports.py`. It requires every `AhlProofs/**/*.lean`
  file found on disk to be reachable by imports from the root module `AhlProofs.lean`, so that
  what was built — and therefore what the environment audit can see — is everything that is
  there. Without it, a file nobody imports is neither compiled nor audited, and both `lake build`
  and the audit exit 0 while ignoring it completely.

### What is checked about this document

`scripts/check_doc_claims.py`, run in CI after the gate, compares this document, `README.md` and
`reports/TOOLCHAIN.md` against what the checks actually print:

* the `./scripts/check_axioms.sh` transcript, the `gen_proof_sha256.py --check` line and the
  regression-fixture table published below must be **verbatim** what those commands produce now;
* every count repeated in a sentence — constants scanned, named theorems and the files they live
  in, files in the hash manifest, fixture runs and failure modes — must equal the computed value,
  in every place it appears;
* the Lean version, release commit and Linux archive digest quoted here must match
  `.github/workflows/ci.yml` and `lean-toolchain`;
* the fixture table below must list exactly the fixtures `scripts/regression_fixtures.py`
  declares.

A claim whose pattern that script can no longer find is a failure there, not a silent skip, so
rewording a checked sentence out of the checker's reach fails CI rather than escaping it.

**Everything else in these documents is maintained by hand and is not machine-checked**: the
mathematical account, the I-D and RFC section references, the lemma tables, the boundary text, the
build timings and the `12 jobs` figure (illustrative and machine-dependent by construction), and
every argument made in prose anywhere. If a sentence here is wrong about the mathematics, no step
of CI will say so. What CI can say is that the numbers and the transcripts are not stale, and it
now does.

### What the four checks are for

Together they protect against **accidental incompleteness**, which is the realistic failure here:
a file added and not imported, a proof left unfinished, a build setting relaxed for one
declaration, a kernel check skipped, a hash manifest that fell out of sync. Each of those is a way
for a green CI run to mean less than it appears to, and each now fails with a named reason. And
they give a reader something reproducible: a clean clone, three commands, the same verdict.

**What they do not protect against, stated just as plainly.** They do not defend against a
participant with write access who changes the checks. `scripts/Audit.lean`,
`scripts/check_imports.py`, `scripts/check_source_policy.py`, `scripts/regression_fixtures.py`,
`scripts/gen_proof_sha256.py` and `.github/workflows/ci.yml` live in this repository and are edited by the same people, in the same
commits, as the proofs they check. `reports/PROOF.sha256` hashes all of them, but it is
regenerated by that same process, so it detects drift *within* a change and not the change
itself. There is no external anchor, no signature over the sources, no attestation from outside
this repository. A reader relying on this evidence is relying on the published CI log for a named
commit, and on review of that commit's diff — the diff of the checks included — not on the checks
being tamper-proof, because they are not.

**The watchdog needs watching too, and this is what it has.** The regression runner is the
component that keeps the other layers honest, so its own failure mode matters: a loop over an
empty fixture list satisfies every assertion in it. That is closed by a roster declared apart from
the fixtures and validated before any of them runs — emptying `FIXTURES`, dropping one fixture, or
duplicating an identifier each fail the run and print the expected roster. It is not closed
against an edit that changes the roster too: `DECLARED_RUNS` sits in the same file. What that edit
costs is three places in one commit, because `scripts/check_doc_claims.py` compares the roster
against the fixture table published in this document. Three agreeing edits is a higher bar than
one, and it is not a guarantee; naming the bar is the honest thing to do with it.

That is the honest shape of the guarantee: strong against forgetting, weak against intent.

## Immutable identifiers

"Revision 0.4" and "v0.3.1" are version words. They name a moving target: from them a reader
cannot recover which bytes this model was read against. Below is the resolvable form. An entry
marked **PLACEHOLDER** is a value this repository does not have; it is named as missing rather
than guessed.

| Artefact | Immutable identifier | Where it resolves |
|---|---|---|
| `ahl-core`, the Rust reference implementation (tag `v0.3.1`) | commit `4c30994df5d37548428785b3615b496800cd31cb` | <https://github.com/evidentum-io/ahl-core/commit/4c30994df5d37548428785b3615b496800cd31cb> |
| `atl-core`, to which `ahl-core` normatively delegates inclusion and consistency verification | commit `79ac9c08585720cbd0de79a31662d99f68efb2f0` (crate version 0.23.2) | <https://github.com/evidentum-io/atl-core/commit/79ac9c08585720cbd0de79a31662d99f68efb2f0> — this is the revision `ahl-core@4c30994`'s `Cargo.lock` pins, not a separately chosen one |
| The conformance vector corpus | `ahl-core@4c30994df5d37548428785b3615b496800cd31cb`, path `test_data/vectors/` | same commit as `ahl-core`; the corpus is not a separate repository |
| The AHL Internet-Draft, "protocol revision 0.4" | **PLACEHOLDER — none exists yet** | see immediately below |

**The Internet-Draft placeholder, and what it needs.** The document this model was read against
is `ahl/docs-md/ahl-protocol-ietf.md`. Its front matter says `docname: draft-zatona-ahl-00`; its
body says "This document defines revision 0.4". Those are two different numbering schemes, and a
reader can resolve neither: the draft has not been submitted to the IETF datatracker (a
`draft-zatona-*` query there on 2026-09-09 returned no documents), and the directory holding the
document is not under version control, so there is no `-NN` revision URL and no commit hash to
cite. Every section number quoted in this repository is accurate for that file as it stood on
2026-09-04, which is a date and not an identifier. To close this, the owner needs to supply one
of:

* a datatracker URL for a submitted revision (`https://datatracker.ietf.org/doc/html/draft-zatona-ahl-NN`); or
* a commit SHA in a repository that publishes the document; or
* a SHA-256 over the exact document bytes, published next to the document.

Until then, "AHL I-D revision 0.4" below and in `README.md` names a document a reader cannot pin,
and this repository says so rather than implying otherwise.

## What is proved

### Lemma 1 — record binding (`AhlProofs/RecordBinding.lean`, over `AhlProofs/Model.lean`)

AHL I-D revision 0.4 (see "Immutable identifiers" — the draft has no resolvable revision
identifier yet), Section 2.6 (preimage injectivity), Section 8.1 (collision-resistance
assumption), Section 8.6 (descriptor binding).

| Clause | Theorem | Conditional on |
|---|---|---|
| 1a | `preimage_injective` | nothing — unconditional, constructive parsing argument |
| 1b (plain) | `commit_plain_collision` | nothing — concludes an *exhibited* collision of `H` |
| 1b (keyed) | `commit_keyed_collision` | nothing — concludes an exhibited collision of `HMAC k` |
| 1c | `descriptor_digest_collision` | `DescriptorModel.jcs_inj` (JCS-INJ, a model parameter) |
| 1c composed | `commit_plain_descriptor_collision` | JCS-INJ |

### Lemma 2 — revocation completeness (`AhlProofs/Closure/RevocationCompleteness.lean`, over
`AhlProofs/Closure/Model.lean`)

AHL I-D Sections 2.4, 5.1–5.4, 7.2, and the Section 7.5.1 erratum 4d. No cryptographic
assumption enters this lemma at all — it is a finite-graph computation over the prefix a
checkpoint commits.

| Clause | Theorem(s) |
|---|---|
| 2a, existence/uniqueness/termination | `closureReach_isLeastClosed`, `isLeastClosed_unique`, `exists_stable`, `mem_closure_reach_iff`, `mem_affected_set_iff` |
| 2b, determinism + decidable disagreement | `affected_of_prefix_eq`, `dispositionsAgree_iff` |
| 2c, monotone in the checkpoint | `affected_mono` |
| 2d, seeding rules genuinely differ | `seeding_rules_differ`, `affected_retraction_ne_correction` |

### Lemma 3 — append-only consistency (`AhlProofs/Tree/AppendOnly.lean`, over
`AhlProofs/Tree/Model.lean`)

RFC 9162 Section 2.1 geometry with AHL I-D Section 2.7 domain separation, over the same abstract
hash as Lemma 1 (`M.H` is a parameter; nothing is assumed about it).

| Clause | Theorem |
|---|---|
| 3a, consistency soundness | `consistency_sound` |
| 3b, inclusion soundness | `inclusion_sound` |
| 3c, enumeration soundness | `range_sound` |
| 3d, composition with Lemma 2 | `affected_mono_of_consistency`, `enumerated_closure_eq` |

Each of 3a–3c concludes the intended property **or an exhibited collision of `H`** — soundness
under the same CR framing as Lemma 1, never an assumption that collisions cannot occur.

Full detail, including the exact I-D sections and the deliberate points where the modelled
verifiers differ from `ahl-core` (e.g. `verifyConsistency` accepting `m = n`), is in `README.md`.

## What is proved over: the model, not the code

Every lemma above is a theorem about the Lean definitions in the three `Model.lean` files —
`Bytes`, `WF`, `pre`, `HashModel` (Lemma 1); `RecordRef`, `Statement`, `Entry`, `ClosureReach`,
`AffectedSet` (Lemma 2); `leafHash`, `nodeHash`, `MTH`, `verifyInclusion`, `verifyConsistency`,
`verifyRange` (Lemma 3). Names were chosen to line up with `ahl-core/src/lib.rs`
(`commit_plain`, `commit_keyed`, `DATASET_SEPARATOR`, `descriptor::validate_dataset_id`) and with
`atl-core` (`hash_children`, `compute_root`, `largest_power_of_2_less_than`) so a reader can hold
model and code side by side — that alignment is a reading convenience, not a theorem, and no
refinement argument connects them.

## What is NOT established

**This is the boundary a citation of this repository must respect.**

1. **No correspondence proof between the Lean model and the `ahl-core` / `atl-core` Rust code.**
   There is no extraction (unlike, e.g., an Aeneas/Charon pipeline) and no refinement argument.
   The Lean definitions were written by reading the I-D and the Rust source; that they match is a
   modelling claim, not a machine-checked one.
2. **The connection that does exist is test evidence, not proof.** The conformance vector
   corpus of `ahl-core` v0.3.1 = commit `4c30994df5d37548428785b3615b496800cd31cb`
   (`test_data/vectors/…` at that commit; see "Immutable identifiers") exercises the real implementation on named
   inputs and records what it does with them — `merkle/`, `checkpoints/`, and receipt vectors
   for Lemma 3; `closure/` (six scenarios, including `retraction-after-correction.json` and
   `supersession-chain.json`, the pair Lemma 2d's proof exhibits) for Lemma 2; the two malformed
   dataset-id vectors for Lemma 1a's `WF` hypothesis. A finite corpus establishes that the named
   inputs at the named revision produce the named outputs — it cannot establish that *every* path
   through the implementation satisfies the model's hypotheses, or that the implementation's
   preimage construction refines `AhlProofs.pre`. The word **bound** is reserved for a refinement
   argument, which does not exist. The Lean results and the corpus results are two separate
   bodies of evidence about the same design.
3. **Each lemma's own boundary file states what that lemma alone does not cover** —
   `AhlProofs/RecordBinding/Boundary.lean` (Lemma 1: correctness of canonicalization, that any
   implementation validates the dataset id, non-disclosure, the CR assumption itself),
   `AhlProofs/Closure/Boundary.lean` (Lemma 2: completeness relative to the declared corpus only,
   nothing about un-anchored derivations, publication completeness, split-view, which entries are
   void or authorized, or time), `AhlProofs/Tree/Boundary.lean` (Lemma 3: the view shown to the
   verifier, not split-view detection; nothing about checkpoint freshness, signatures, or log
   keys; soundness only, not completeness, of the RFC 9162 proof systems).
4. **Collision resistance of SHA-256 / HMAC-SHA-256 is assumed, not proved**, and is not even
   stated as a hypothesis anywhere in the Lean code — see Lemma 1's assumption list in
   `README.md`. The lemmas conclude an *exhibited* collision rather than assuming none exists,
   which is the correct direction for an unconditional result but is not itself a
   collision-resistance proof of anything.

## Axiom audit

`scripts/check_axioms.sh` is the gate's single entry point and runs three layers in order: the
import invariant (`scripts/check_imports.py`), the policy over source text
(`scripts/check_source_policy.py`), and then the audit proper. Only the third layer is a
semantic check, and it is the subject of this section; the other two are described under "Trust
boundary" above and are there to make sure the third one is looking at everything and cannot be
made to look at nothing. A failure in either of the first two aborts before the audit runs, so
the audit never reports on a tree that already failed a structural check.

The audit itself examines **every** constant this repository is responsible for, not a curated
subset and not a text-based discovery pass over the `.lean` sources. It runs
`scripts/Audit.lean` — a Lean file that imports the already-built `AhlProofs` library and walks
the compiled `Lean.Environment` (`env.constants`) directly, via `Lean.collectAxioms`, the same
primitive `#print axioms` itself calls.

**Why the environment, and not the source text.** An earlier version of this audit discovered
its targets by regex-parsing the `.lean` files (`scripts/list_theorems.py`, feeding
`scripts/check_axiom_output.py`). That approach was retired after two proven blind spots — both
confirmed by appending the fragments below to `AhlProofs/Model.lean`: the build passed and the
old audit printed a clean PASS on a tree that, in fact, contained an axiom and a `sorry`.

1. **Visibility modifiers.** The old target regex matched only a line beginning with the bare
   keyword `axiom`. `private axiom sample_a : False` was invisible to it, and the `example` that
   can carry a reference to such a declaration never appeared in its target list at all — no
   keyword the old regex looked for begins an `example`.
2. **Comments vs. string literals.** The old comment-stripper did not know about string literals.
   A string literal containing the two characters `/-` makes it start treating the following text
   as a block comment until the next occurrence of `-/`-like characters, silently deleting any
   declaration in between. Separately, its `sorry` search matched the word `sorry` on a word
   boundary — which does not match `sorryAx`, the actual term `sorry` elaborates to.

Both classes are closed constructively by working over the compiled environment rather than by
patching the regex for these two specific cases: a declaration that exists after elaboration is,
by definition, in `env.constants` — visibility modifiers and name-mangling change *how* it is
named there, never *whether* it is there — and there is no comment syntax or string literal to
mis-parse, because nothing here reads source text at all.

**What is checked, over every constant whose home module is under `AhlProofs.*`** (not only
`theorem`/`lemma` — `def`, `instance`, `private` declarations and automatically generated
auxiliary lemmas alike; currently 645 constants, against the 102 named `theorem`/`lemma`
declarations `scripts/list_theorems.py` counts for the prose numbers elsewhere in this
document — see "Two counts, two purposes" below):

* No `axiom` declared by this repository. Any `ConstantInfo.axiomInfo` found in an `AhlProofs.*`
  module is, by construction, one of ours: the trusted kernel axioms live in `Init`/`Lean`
  modules, never here.
* No axiom outside `{propext, Classical.choice, Quot.sound}` in the transitive closure of any
  constant. This subsumes the `sorry` check without a separate text search: `sorry` elaborates to
  the axiom `sorryAx` (`Init/Prelude.lean`), so a `sorry` anywhere in a closure is just another
  name that fails the same "outside the allowed set" test a stray `axiom` would fail.
* The `priority-zero.md` claim — the set of constants whose closure contains `Classical.choice`
  is *exactly* `{AhlProofs.commit_plain_descriptor_collision}` — checked against every one of the
  645 constants, not only the 102 named theorems, and it still holds exactly at that finer grain:
  no automatically generated helper anywhere in the library pulls in choice by accident.

**Two counts, two purposes.** `scripts/list_theorems.py` still exists and is unchanged in what it
is *for*: counting the named `theorem`/`lemma` declarations for the prose numbers in this document
and in `README.md` (102, in 10 files — see "What is proved" above). It is no longer part of the
audit pipeline and its output is not fed to anything security-relevant; its own comment-stripper
has the same string-literal blind spot described above; a script whose count is only ever read by
a human is a different risk profile than one whose output gates a claim. `scripts/Audit.lean`
does not count named theorems at all — it scans every constant the compiler produced — which is
exactly why it does not need a target list, correct or otherwise: the target list and the build
are the same event, so nothing can build without being audited, and nothing that is audited was
found by pattern-matching keywords.

There is no static per-theorem manifest file in this repository, and no target-discovery step
whose output could be truncated to empty and still look like success: `scripts/Audit.lean` fails
outright if it scans zero constants under `AhlProofs.*`, and `env.constants` cannot be empty for
a library that just finished building — the two conditions cannot both hold.

### Required regression tests

**7 fixture runs covering 6 failure modes** — six ways for this pipeline to be wrong, one of them
exercised twice with a different set of layers active (see 6 and 6b below). Each run must make the
pipeline exit nonzero **and must be caught by the layer responsible for it** — a fixture that
failed for some unrelated reason would satisfy "exits nonzero" and prove nothing.

**This is a test, not a report of one.** `scripts/regression_fixtures.py` applies every fixture
and asserts the exact exit status of every stage (`lake build`, import invariant, source policy,
environment audit, hash manifest), the identity of the layer that must fail, and a substring that
layer's output must contain. `.github/workflows/ci.yml` runs it on every push and every pull
request, immediately before the ordinary gate — so the gate then has to pass on the same tree,
which is what demonstrates the fixtures left nothing behind. An earlier version of this section
described the same fixtures in the present tense on the strength of a person having run them
once by hand; nothing re-established that, and nothing would have noticed a layer being removed
while this prose went on describing it.

**The runner cannot pass while running nothing.** `FIXTURES` is a list, and a loop over an empty
list satisfies every assertion in it — which is how an earlier version of this runner could be
emptied and still print success, the same defect that got this repository's first static audit
manifest rejected. `scripts/regression_fixtures.py` therefore declares its roster separately
(`DECLARED_RUNS`, `DECLARED_MODES`) and validates the fixtures against it *before* the first one
runs: the exact identifiers, in that order, with no duplicates, no additions and no omissions,
each carrying a layer under test that is itself declared to fail and an expected reason string.
Emptying the list, deleting one fixture, or duplicating an id each fail the run with the roster
printed. What this does not close is an edit to `DECLARED_RUNS` in the same commit — that is
stated under "Trust boundary", along with the third place the same edit would have to be made.

**How the working tree is kept clean.** The runner never writes to the working tree. Every
fixture is applied to a fresh copy of the repository in a system temporary directory (`.git`,
`.lake` and `__pycache__` excluded), the pipeline runs there, and the copy is deleted in a
`finally` block. Because the copy lives outside the repository, a fixture's `.lean` file is
outside the globs `scripts/check_source_policy.py` and `scripts/gen_proof_sha256.py` walk: it
cannot enter the hash manifest and cannot enter the built library. That is the guarantee by
construction; it is also verified, within a scope worth stating exactly. The runner takes a
SHA-256 snapshot before the first fixture and again after the last of every file under the real
root **except `.git/`, `.lake/` and `__pycache__/`** — git metadata, build output and bytecode
caches, none of them repository content — and fails if a single byte, path, addition or deletion
differs among the files it hashes. Those three are safe to omit rather than merely convenient:
the runner never invokes git and never builds in the real tree, only in the copies. The published
summary line names the exclusions and the file count, so the scope of the claim travels with it.

The table below is the runner's own output on the tree this document describes (`0` = the stage
exited 0, `1` = exited nonzero, `-` = not run):

```
 fixture     layer     build   imports    policy     audit  manifest
       1   imports         0         1         0         0         0   ok
       2    policy         0         0         1         0         0   ok
       3    policy         0         0         1         0         0   ok
       4     build         1         0         1         -         0   ok
       5     audit         0         0         0         1         0   ok
       6  manifest         0         1         0         0         1   ok
      6b  manifest         0         0         0         0         1   ok

all 7 fixture run(s) covering 6 failure mode(s) behaved as declared: each broke the pipeline, and each was caught by the layer named for it. Working tree unchanged (28 file(s) hashed before and after, excluding .git/, .lake/, __pycache__/).
```

| # | Fragment | Layer under test | Why that layer, and why not another |
|---|---|---|---|
| 1 | `AhlProofs/Extra.lean`, containing `axiom planted_bad : False`, never added to `AhlProofs.lean` | import invariant | The build and the environment audit are blind here by construction: an unimported file is never compiled, so no constant of it exists to audit. This is the ordinary case of forgetting an `import` line, and it produces a repository whose green CI says nothing at all about that file. |
| 2 | `set_option warningAsError false in` / `example : False := <placeholder>` | source policy | Two forbidden lexemes at once. The environment audit cannot see this: an `example` is elaborated and discarded, never stored in `env.constants`, and the local `set_option` removes the build failure Lean's own warning would otherwise cause. |
| 3 | `set_option debug.skipKernelTC true in` + a `run_tac` proof assigning `True.intro` to a goal of `False` | source policy | Lean 4.31.0 accepts this with exit 0 and a **clean** axiom closure — no placeholder axiom, no axiom of our own — because the kernel never re-checked the term. No walk over `env.constants` can detect it; only refusing the lexeme can. |
| 4 | `theorem probe_incomplete : True := by <placeholder>` | `lake build` | `declaration uses 'sorry'` is a warning promoted to an error by `lakefile.toml`. The source policy also rejects the lexeme (the runner asserts both), and the environment audit would have found `sorryAx` in the constant's closure had the build been allowed to finish — hence `-` for the audit stage: with no `.olean`s, its exit status would say nothing about the audit. |
| 5 | `axiom probe_axiom : False` | environment audit | Both of the audit's own-axiom findings fire: `own axiom declaration(s), not part of Lean's trusted kernel` and `axiom closure is not a subset of the allowed set`. Declaring an axiom is not a Lean warning, so the build is untroubled by it. |
| 6 | A new `.lean` file under `AhlProofs/`, manifest left stale | hash manifest | In this plain form the import invariant fires too; the runner still requires the *manifest* check to fail, so the fixture cannot pass on the strength of another layer. |
| 6b | The same file, with its `import` line added | hash manifest | The import invariant now passes, leaving the manifest check as the only thing between the tree and a green run. This is what establishes that the two layers are independent rather than one masking the other — the claim is machine-checked here rather than asserted in prose. |

For fixtures 1 through 5 the runner regenerates the manifest inside the copy after applying the
fixture, so manifest staleness cannot be what fails and the named layer is demonstrably the one
doing the work. Fixtures 6 and 6b leave it stale, because there staleness is the subject.

Fixtures 1 through 3 previously passed the whole pipeline with exit 0; `scripts/check_imports.py`
and `scripts/check_source_policy.py` are what closed them.

One thing the runner cannot check about itself: that it would notice a layer being removed. That
was established once, by hand, on 2026-09-09 — a copy of this repository with
`scripts/check_source_policy.py`'s finding list emptied made the runner report fixtures 2, 3 and 4
as FAILED with `stage policy: expected exit 1, got 0`, and fixtures 2 and 3 additionally as
`the pipeline exited zero everywhere`, which is exactly the state this repository was in before
that layer existed. Repeating it takes a copy of the tree and two minutes; it is a manual check
and this document does not claim otherwise.

### Build warnings are errors

`lakefile.toml` sets `leanOptions = [["warningAsError", true]]`. `lake build` now fails on any
Lean warning, `declaration uses 'sorry'` foremost: the compiler already flags every `sorry`
itself as it elaborates each declaration, so turning that specific warning into a build failure
is a second, independent, and much cheaper check of the same "no `sorry`" claim the environment
audit above makes — cheaper because it costs nothing beyond the build that runs anyway, and
independent because it does not go through `Lean.collectAxioms` at all. Confirmed to change no
outcome on the actual proof sources: a full `lake clean && lake build` with this option set
still completes all 12 jobs with no warnings (see "Live run" below).

**A known consequence, and it is kept anyway.** `warningAsError` promotes *every* Lean warning,
not only `declaration uses 'sorry'`. Lean's warning set changes between releases, so a future
toolchain may warn about something this code does today — an unused variable, a renamed or
deprecated prelude lemma, a newly linted piece of style — and the build will then fail for a
reason that has nothing to do with the proofs. That is the expected failure mode of a toolchain
bump in this repository, and it is a cost accepted deliberately: the alternative is a build that
can go green while `declaration uses 'sorry'` is on screen. When it happens, the fix is to
address the new warning, not to relax the setting — and relaxing it locally for one declaration
is itself refused, because `scripts/check_source_policy.py` rejects `warningAsError` set to false
in any `.lean` file (regression fixture 2).

### The `priority-zero.md` claim, checked on every constant, on every run

`ahl/docs-md/priority-zero.md` states: "Без `sorry`/`axiom`; `Classical.choice` только в
`commit_plain_descriptor_collision`." Verified with Lean `leanprover/lean4:v4.31.0`
(`lean-toolchain`, commit `68218e876d2a38b1985b8590fff244a83c321783`), against all 645
constants under `AhlProofs.*` — full output; this is what `./scripts/check_axioms.sh` prints,
reproducible on any revision since nothing here is a one-time snapshot:

```
== layer 3/3: scripts/Audit.lean (environment-based axiom & placeholder-proof audit) ==
scanned 645 constant(s) whose home module is `AhlProofs` or under it (every kind of declaration, not a curated subset of theorems)
own axiom declarations: (none)
sorryAx present in the closure of: (none)
Classical.choice used by: #[AhlProofs.commit_plain_descriptor_collision]
axiom(s) outside the allowed set [propext, Classical.choice, Quot.sound]: (none)
extra axioms: (none) PASS

```

**Result: the claim holds exactly**, checked against every constant the compiler produced, not a
hand-picked subset of named theorems. `Classical.choice` appears in the axiom footprint of
exactly one constant in the entire repository — `commit_plain_descriptor_collision` — and
nowhere else, including every automatically generated helper. No `sorry` (`sorryAx`) appears in
the closure of anything. The only three axioms used anywhere in the development are `propext`,
`Classical.choice` (that one constant) and `Quot.sound`. This is not a one-time sweep recorded
here and then trusted forever: `scripts/check_axioms.sh` recomputes it — over whatever
`env.constants` contains after the current build, not a fixed list — on every push and pull
request, and fails the build the moment it stops holding.

## Live run

Lean `leanprover/lean4:v4.31.0` (`lean-toolchain`, commit `68218e876d2a38b1985b8590fff244a83c321783`).
No Mathlib, `lake-manifest.json` package list is empty. This is a real transcript, reproduced by
running the commands below verbatim; timings vary by machine and by filesystem cache state (see
`reports/TOOLCHAIN.md`) and are illustrative, not a performance claim.

### `lake clean && time lake build`

```
$ lake clean && time lake build
✔ [2/12] Built AhlProofs.Model (299ms)
✔ [3/12] Built AhlProofs.Closure.Model (327ms)
✔ [4/12] Built AhlProofs.RecordBinding (203ms)
✔ [5/12] Built AhlProofs.RecordBinding.Boundary (169ms)
✔ [6/12] Built AhlProofs.Tree.Model (415ms)
✔ [7/12] Built AhlProofs.Closure.RevocationCompleteness (502ms)
✔ [8/12] Built AhlProofs.Closure.Boundary (146ms)
✔ [9/12] Built AhlProofs.Tree.AppendOnly (765ms)
✔ [10/12] Built AhlProofs.Tree.Boundary (135ms)
✔ [11/12] Built AhlProofs (136ms)
Build completed successfully (12 jobs).

real	0m2.026s
user	0m3.681s
sys	0m1.048s
```

Recorded on aarch64-apple-darwin (macOS), warm toolchain cache, cold `.lake/build` — the same
machine and conditions as `reports/TOOLCHAIN.md`. CI times the same command independently on
`ubuntu-latest` on every run; see the `lean` job of `.github/workflows/ci.yml`.

The gate (`./scripts/check_axioms.sh`) is separate from the timing above: its first two layers
read the working tree and need no toolchain, and its third is its own `lake env lean` invocation
against the `.olean`s this build produced.

### `./scripts/check_axioms.sh`

The whole gate, verbatim, on the tree this document describes — exit status 0:

```
$ ./scripts/check_axioms.sh
== layer 1/3: scripts/check_imports.py (import invariant) ==
import invariant holds: 9 file(s) under AhlProofs/, all reachable from AhlProofs.lean (10 module(s) in the transitive closure)

== layer 2/3: scripts/check_source_policy.py (policy over source text) ==
source policy holds: 11 .lean file(s) scanned, none contains `sorry`, `admit`, `warningAsError false`, `debug.skipKernelTC`

== layer 3/3: scripts/Audit.lean (environment-based axiom & placeholder-proof audit) ==
scanned 645 constant(s) whose home module is `AhlProofs` or under it (every kind of declaration, not a curated subset of theorems)
own axiom declarations: (none)
sorryAx present in the closure of: (none)
Classical.choice used by: #[AhlProofs.commit_plain_descriptor_collision]
axiom(s) outside the allowed set [propext, Classical.choice, Quot.sound]: (none)
extra axioms: (none) PASS
```

Nine files under `AhlProofs/` plus the root module and `scripts/Audit.lean` make the eleven
`.lean` files layer 2 scans; the ten modules of the import closure are the nine plus the root.
Layer 2's report line lists the forbidden lexemes literally, which is the one place in this
repository where they are allowed to appear — it is generated output, not a `.lean` file.

### Binding: what `reports/PROOF.sha256` does and does not give you

`reports/PROOF.sha256` is generated by `scripts/gen_proof_sha256.py`, which hashes the toolchain
pin, the lake project files, every `.lean` file under the library and under `scripts/`
(discovered by the same glob `scripts/list_theorems.py` uses for the library files — not a
hand-maintained list, so a *new* `.lean` file cannot go unaudited without this check noticing the
manifest is stale), every audit script, and `.github/workflows/ci.yml` itself:

```
$ python3 scripts/gen_proof_sha256.py --check
reports/PROOF.sha256 is current (22 file(s))
```

CI runs this check first. **What this manifest is, and is not.** It is a same-commit
internal-consistency check, not a proof of integrity or provenance: the manifest is generated
from, and committed alongside, exactly the files it lists, by the same process that could edit
any of them, so it gives no protection against a party who can alter the repository outright.
What it gives is protection against silent drift inside a single change — a file's content
changing without `reports/PROOF.sha256` being regenerated to match is a CI failure, not a quiet
inconsistency. It is deliberately narrower than "every file in the repository": `README.md`,
this file and `reports/TOOLCHAIN.md` are prose that can be edited without changing what the build
or the audit compute, and are not hashed. The workflow YAML *is* hashed, unlike an earlier
version of this manifest — the workflow is what determines whether the audit step runs at all, so
excluding it would let a change that quietly deleted the audit step pass unnoticed by this check.

## Reproduce

```sh
git clone https://github.com/evidentum-io/ahl-proofs.git
cd ahl-proofs
python3 scripts/gen_proof_sha256.py --check
lake clean && time lake build
python3 scripts/regression_fixtures.py
./scripts/check_axioms.sh
python3 scripts/check_doc_claims.py
```

`scripts/regression_fixtures.py` is the slowest of these — it builds the library once per
fixture, in a throwaway copy — and it is the one that checks the checks; running it last, after
the gate, works equally well, since it does not touch the working tree either way.

Install the toolchain first, from the checksummed release archive — `reports/TOOLCHAIN.md`'s
"Install" section is the same pinned URL, the same SHA-256 comparison and the same version check
that `.github/workflows/ci.yml` performs, so a local run and a CI run establish the same thing
about the toolchain. `.github/workflows/ci.yml` is the authority on the exact commands CI runs,
on every push (any branch) and every pull request; read it alongside "Trust boundary" above,
which says what a passing run of all of this does and does not mean.
