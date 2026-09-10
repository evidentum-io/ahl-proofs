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
* **The regression fixtures** — `scripts/regression_fixtures.py`. 38 fixture runs covering 19
  failure modes of this repository, each applied to a throwaway copy of it, each required to fail
  *and* to fail at the layer that owns it, *and* to fail `./scripts/check_axioms.sh` itself with
  the diagnostic that names that layer. This is what keeps the other three honest: a layer that stopped working
  would turn a fixture green, and a green fixture is a red CI run. It is run in CI immediately
  before the gate, so the gate has to pass on the same tree afterwards. See "Required regression
  tests".
* **Artifact coverage and the import invariant** — `scripts/check_imports.py`. Two rules, the
  second because the first was not enough. Every file in the working tree whose suffix is one this
  repository covers — `.lean`, `.py`, `.sh`, `.yml`, `.yaml` — must fall into a **declared**
  category and must be hashed by `reports/PROOF.sha256`:

  | Suffix | Declared category |
  |---|---|
  | `.lean` | a library module (`AhlProofs.lean` or a file under `AhlProofs/`), or a file named in `DECLARED_AUXILIARY` |
  | `.py`, `.sh` | tooling under `scripts/`, at any depth |
  | `.yml`, `.yaml` | a file named in `DECLARED_YAML` |

  Alongside it, `DECLARED_BUILD_FILES` names the build and pin files — `lean-toolchain`,
  `lakefile.toml`, `lake-manifest.json` — which carry no covered suffix and so fall outside the
  table above. `scripts/gen_proof_sha256.py`'s own mandatory list must equal that set plus the
  root module plus `DECLARED_YAML`, exactly; dropping an entry from either file is a failure
  rather than a shorter, passing manifest. **That set is declared, not derived**, and the reason
  is worth stating: Lake exposes no command that enumerates what it reads, and "everything in the
  repository root" would sweep in the prose and the licence. What is constructive is only this —
  Lake reads `lakefile.toml` or `lakefile.lean`, and the second is a `.lean` in the root, which
  the coverage rule already refuses as unclassified, so the build cannot be driven from a file the
  rule does not see.

  And every library module must be reachable by imports from the root module, so that what was
  built — and therefore what the environment audit can see — is everything that is there.
  "Hashed" is not restated here: the rule asks `scripts/gen_proof_sha256.py` for its own file
  list, so classification and hashing cannot drift into meaning different sets.

  **Why those five suffixes and no others.** Something outside the list can only run if the build
  or a CI step invokes it. The build is Lake, which reads `lakefile.toml` (a mandatory manifest
  entry) or `lakefile.lean` (a `.lean`, so already refused unless classified) and compiles
  `.lean`. CI invokes exactly `python3 scripts/*.py`, `./scripts/*.sh`, `lake`, `lean`, `curl`,
  `tar`, `find` and a `sha256` comparison, and its step list cannot grow without failing the
  install-script label check. YAML is on the list for a reason none of the others share: GitHub
  Actions runs every file under `.github/workflows/` on its own schedule and permissions, without
  any step of ours referring to it. A `Makefile`, a `Dockerfile`, a `.js` — nothing here reads
  them; they are inert until one of the files above changes, and every one of those is a mandatory
  manifest entry. The argument rests on the current build and CI, and would have to be revisited
  if either grew a new interpreter.

  The second rule alone left a file nobody imports uncompiled and unaudited, with `lake build` and
  the audit both exiting 0. Four times now a Lean file has turned out to sit somewhere *no* check
  looked: under `AhlProofs/` unimported; under `scripts/` in a subdirectory a non-recursive glob
  missed; in the repository root, where `axiom planted_at_root : False` passed the manifest, the
  import invariant, the source policy, `lake build` and the whole gate; and — the same hole
  arriving from the other side — under `.git/`, `.lake/` or `__pycache__/`, which classification
  *excluded*, so the file was neither classified nor refused while this layer printed
  "0 unclassified". Each time the fix had been to walk one more directory, which is how the next
  place stays available.

  Both directions are closed now. A file that belongs to no declared category fails, with its path
  and what to do about it; and a `.lean` under one of the three excluded directories is **refused**
  rather than classified, because none of them holds a Lean source in this project — it takes no
  dependencies, so Lake never places sources under `.lake/` — and there is therefore no legitimate
  case to distinguish. The three checks that walk the tree share one definition of that area
  instead of each keeping a copy, so they cannot drift apart.

  **The exact scope of this guarantee**, stated so it does not read wider than the code: a *Lean
  file* here is a **regular file whose name ends in exactly `.lean`**. A file whose suffix merely
  case-folds to that (`Bad.LEAN`) is refused rather than left uncovered, and directory symbolic
  links anywhere outside `.git/` are refused too, since one would make "this repository's files"
  depend on something outside the repository. What is *not* covered is a file with Lean content
  and no `.lean` suffix: nothing here reads file contents to guess a language, and no claim is
  made that it does.

### What is checked about this document

`scripts/check_doc_claims.py`, run in CI after the gate, compares this document, `README.md` and
`reports/TOOLCHAIN.md` against what the checks actually print. **This is the exhaustive list** —
if something is not on it, it is not machine-checked, whatever else these documents say:

1. **Four published transcripts, located as exactly one fenced block each, inside the section
   named for it.**
   * `./scripts/check_axioms.sh` — equal, character for character, to what the gate prints now.
   * `python3 scripts/gen_proof_sha256.py --check` — likewise.
   * the regression-fixture table — equal to what `scripts/regression_fixtures.py
     --expected-table` renders.
   * `lake clean && time lake build` — checked for the part of it that is reproducible: the set
     of modules built and the job count lake reports. **Its timings are not checked** and are not
     checkable; they differ between machines and between runs on one machine, and are labelled
     illustrative where they appear.
   "Exactly one block" is part of the check: a second, stale copy of any of these elsewhere in the
   document is a failure, not something a substring search would have missed.
2. **Counts, in every place each appears**: constants scanned by the audit, named
   `theorem`/`lemma` declarations and the number of files they live in, files in the hash
   manifest, fixture runs and failure modes, and the lake job count.
3. **The toolchain pin**: the tag `leanprover/lean4:v…` wherever these documents spell it out, the
   release commit, the version inside the recorded `lean --version` line, and **all four**
   platform archive digests offered by `reports/TOOLCHAIN.md` — not only the one CI installs,
   whose value must additionally equal `.github/workflows/ci.yml`'s.
4. **The fixture roster**: the table below must list exactly the fixtures
   `scripts/regression_fixtures.py` declares, in order.
5. **The install script published in `reports/TOOLCHAIN.md`.** That script is the one runnable
   artefact this repository publishes and does not run — CI does not execute it, and neither do
   the fixtures — and it silently drifted from the workflow once for exactly that reason. Two
   checks now hold it:
   * **It exists once, and it parses.** Exactly one `#!/bin/sh` block in the whole document,
     inside the Install section, and `sh -n` on it exits 0. *This establishes syntax, not
     behaviour*: it catches a block that has stopped being a valid shell script, or has gone
     missing, or has been published twice with one copy stale. It says nothing about whether the
     script installs the right toolchain or runs the right checks, because nothing here executes
     it.
   * **It selects the recorded archive for every recorded platform.** The script's
     `# --- platform selection` block is **parsed, never executed**: the `case` on
     `"$(uname -s)/$(uname -m)"` is read branch by branch, in one accepted form, and anything
     outside that form fails rather than being run to find out what it does. Each of the four
     branches must be **exactly** the declared set — five, counting `Linux/arm64` as a written-down
     alias of `Linux/aarch64` — each mapping to its platform's archive paired with that platform's
     recorded digest. Exactly, because "the recorded platforms are covered" was not enough: an
     extra `FreeBSD/x86_64)` branch selecting the Linux archive left every required branch and the
     `*)` default in place and the set of offered archives unchanged, while FreeBSD quietly
     stopped being refused. There must also be a `*)` branch that assigns no archive and exits
     nonzero, so an unrecorded platform is refused rather than handed some other platform's build;
     and the pair for the runner's platform must be the pair `.github/workflows/ci.yml` installs. This exists
     because a constant is exactly what went wrong: the script once hard-wired one platform, so a
     reader on Linux — the platform CI runs on — would have unpacked a macOS build. An earlier
     version of *this check* ran the fragment with a stubbed `uname`, which answered the question
     but overstated its own safety: it executed text from a Markdown file in the working
     directory, with only `uname` shadowed and no timeout. Parsing a known small form is both
     stricter and free of that.
   * **The order and identity of the workflow's steps are machine-checked against the published
     install script's labels; what each step actually runs is not, and is maintained by hand.**
     A comparison of command sets lived here and was **removed**. It produced two defects of
     its own in two rounds: it first
     treated shell it could not read as no commands at all — so `CI_X=1 node …`, `command node …`,
     `trap 'node …' EXIT` and `if node …; then` all compared as equal — and then, once that was
     fixed, it turned out to declare `rm`, `mv`, `mkdir`, `cd` and `export` indifferent, so
     `rm -f reports/PROOF.sha256` appended to the published script would have compared as no
     change at all. The rule agreed in advance was that a second defect in that machinery meant
     deleting it rather than repairing it a third time, and it was deleted. **Which commands each
     step runs, and whether the published script runs the same ones, is maintained by hand and
     rests on review of the diff.** What survives is the label check below: the *identity and
     order* of the steps, which is simple, checkable, and catches a step added, removed or
     reordered.
   * **The workflow, the job and every step fit a strict schema.** At the top level the admitted
     keys are `name`, `on`, `jobs`; the triggers must be exactly `push` and `pull_request`, each
     without a filter, which is what makes "every push, any branch" a checked claim rather than
     prose; the declared jobs must be exactly `lean`; that job may declare only `runs-on`,
     `timeout-minutes`, `env` and `steps`, its `runs-on` must be the declared runner image, and
     its `env` must be exactly the four toolchain values — a `PATH` there would silently decide
     which `python3` and which `lean` the steps see. A step is `name` plus exactly one of `run:`
     or a `uses:` pinned to a 40-character commit SHA — and nothing else. Not a list of dangerous
     fields but a list of admitted ones, so `if:`, `continue-on-error:`, `shell:`,
     `working-directory:`, `env:`, `with:` and anything GitHub adds later are all refused until
     someone decides what this checker should make of them. This is here because its absence was
     the largest hole found in twelve rounds: `if: false` on the regression-fixtures step, with
     the manifest regenerated as any author would regenerate it, produced a green CI run that
     never executed a single fixture — the label check saw the step, the command comparison saw
     the same commands, and nothing saw that the step would not run. The same schema was then
     found to be closed at the wrong *depth*: `if: false` beside `runs-on:` disables the job and
     every step-level check goes on reporting that the steps are exactly right, so the levels
     above a step are now admitted-key lists too.
   * **Its `# CI step N [key].` labels match the workflow.** Expanded, the labels must cover
     `.github/workflows/ci.yml`'s steps exactly once each, in order, with each label's key
     occurring in that step's `name`. A step added to, removed from or reordered within the
     workflow while the script stays as it was fails this, with a line-by-line comparison in the
     output. `.github/workflows/ci.yml` is the source of truth and is read structurally rather
     than by regex over its text — by a small dependency-free reader that **rejects** anything
     outside the shape this workflow has rather than reading it literally: YAML anchors and
     aliases, merge keys, trailing comments on a `name:`, escaped or flow-style scalars, tabs,
     document markers, and any nesting inside a step (a `with:` block's own `name:` is not the
     step's name) all fail the run instead of being guessed at. Where PyYAML happens to be
     installed its parse is compared against the reader's and a disagreement fails; the library is
     never required. *This establishes the order and the identity of the steps,
     not that each step's contents are equivalent*: a label can point at the right step while the
     shell under it does something else. That equivalence is not machine-checked, and is not
     claimed to be.

A claim whose pattern that script can no longer find is a failure there, not a silent skip, so
rewording a checked sentence out of the checker's reach fails CI rather than escaping it.

**Everything not in that list is maintained by hand and is not machine-checked.** Concretely, and
not as a hedge: the mathematical account and every argument made in prose; the I-D and RFC section
references; the lemma tables; the boundary text; the build timings; the host triple and local
`lake` path recorded at the top of `reports/TOOLCHAIN.md`, which are a record of one past run on
one machine and cannot be re-derived here; **the absence of statements that contradict the
canonical scope sentence** — its *presence* in all three documents is required and checked, so the
boundary always travels beside the promise, but nothing prevents a second sentence nearby from
promising more; what the published install script actually *does* when
executed, as opposed to that it parses and is labelled in step with CI; **which commands each
workflow step runs, and whether the published script runs the same ones** — the comparison that
checked this was removed after two defects of its own, and it is now maintained by hand and rests
on review of the diff; **an `axiom` appended to a declared auxiliary Lean file after the audit's
own evaluation point** — inert, since nothing imports it and the audit has already run, but
unreported; and the correctness of any English sentence about any of it. If a sentence here is wrong about the mathematics, no step of CI will say so. What CI can
say is that the numbers, the pins and the transcripts are not stale, and it now does.

### What the four checks are for

Together they protect against **accidental incompleteness**, which is the realistic failure here:
a file added and not imported, a proof left unfinished, a build setting relaxed for one
declaration, a kernel check skipped, a hash manifest that fell out of sync. Each of those is a way
for a green CI run to mean less than it appears to, and each now fails with a named reason. And
they give a reader something reproducible: a clean clone, one toolchain install and the five
commands listed under "Reproduce" below, and the same verdict.

**What they do not protect against, stated just as plainly.** They do not defend against a
participant with write access who changes the checks. `scripts/Audit.lean`,
`scripts/check_imports.py`, `scripts/check_source_policy.py`, `scripts/regression_fixtures.py`,
`scripts/gen_proof_sha256.py`, `scripts/check_doc_claims.py` and `.github/workflows/ci.yml` live in
this repository and are edited by the same people, in the same commits, as the proofs they
check. `reports/PROOF.sha256` hashes all of them, but it is
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

**Every roster is in the repository it governs, and that includes the coverage rule's.**
`DECLARED_AUXILIARY`, `DECLARED_YAML`, `DECLARED_BUILD_FILES`, `EXCLUDED_DIRS` and the
covered-suffix set all sit in `scripts/check_imports.py`; `DECLARED_PLATFORM_BRANCHES`, `DECLARED_USES` and the workflow, job and
step schemas (`WORKFLOW_SCHEMA_KEYS`, `JOB_SCHEMA_KEYS`, `STEP_SCHEMA_KEYS`,
`DECLARED_JOBS`, `DECLARED_TRIGGERS`, `DECLARED_RUNNER`, `DECLARED_JOB_ENV`) sit in
`scripts/check_doc_claims.py`. Adding a directory to the exclusions, or a file to either declared
list, is a one-line change that re-opens exactly the area the rule closes — and nothing but review
of the diff will say so. This is not a defect in the rule; it is the same same-commit limit every
declared roster here has, and it cannot be removed from inside the repository. It is worth stating
plainly for this one because the coverage rule is the check that says "everything is accounted
for", and a reader should know what that sentence rests on: a list that a writer can edit in the
commit that needs it edited.

**The document checker has the same shape of weakness, and less protection.**
`scripts/check_doc_claims.py` refuses to run with an empty claim list, and every claim it holds
must match at least one place in the documents — so a checked sentence cannot be quietly reworded
out of its reach. But **the list of claims is maintained by hand**: deleting one entry from a
non-empty list is a green run, exactly as deleting one fixture from the roster would be if the
roster were not declared separately. There is no equivalent of `DECLARED_RUNS` here, because the
set of interesting sentences in a prose document is not something this repository can enumerate
from anything but itself. So the exhaustive list under "What is checked about this document" is a
statement of intent kept in sync by review, not by machine. Read it as: these are the claims CI
will catch drifting; a claim removed from that script stops being caught, and only the diff would
show it.

**What else is trusted, unverified.** Naming Lean's kernel as trusted is the usual disclaimer and
it is not the whole list. Everything below runs on machinery this repository does not check and
cannot check:

* **The CI runner and its image.** `actions/checkout` is pinned by commit SHA; `ubuntu-latest` is
  not pinned at all — it is a moving image, rebuilt by GitHub, and every job here executes inside
  it. The runner itself is GitHub's infrastructure.
* **The system utilities every step depends on**: `curl` to fetch the archive, `sha256sum` to
  compare its digest, `tar`/`zstd` to unpack it, `bash`/`sh` to sequence any of it, `find`,
  `python3` for four of the five checks, and the `$GITHUB_PATH` mechanism that makes the installed
  toolchain visible to later steps.
* **`lean` and `lake` themselves**, beyond the digest: the digest establishes which bytes were
  written to disk, not what those bytes do.

The consequence has to be said plainly, because the digest check reads stronger than it is: on a
compromised runner, `sha256sum` can print `OK`, `lean` can print the expected version and release
commit, and the gate can exit 0, all without any of it being true. "The bytes unpacked and run are
the bytes whose SHA-256 is recorded" is a claim about what the *procedure* does when the tools
executing it are honest — it is not, and cannot be, a claim about a host that has been subverted. What the
digest genuinely rules out is a substituted or corrupted *download* on an honest host, which is
the realistic threat and the reason it is there.

None of this is an argument against the checks; it is the boundary of what a repository can
establish about itself from inside itself. A reader who needs more than this needs attestation
from outside — a signed build, a reproducible-build comparison against an independent rebuild, or
their own run on their own machine, which the "Install" section of `reports/TOOLCHAIN.md` exists
to make possible.

That is the honest shape of the guarantee: strong against forgetting, weak against intent, and
resting on a host and a toolchain it takes on faith.

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

**38 fixture runs covering 19 failure modes** — nineteen ways for this pipeline to be wrong;
several modes take more than one run because the same mistake has more than one spelling. Mode 6
is exercised twice with a different set of layers active (6 and 6b), mode 7 once per forbidden
lexeme (7a–7d), because a policy rule that no fixture exercises can be deleted without turning
anything red, mode 9 once per place a Lean file has actually turned up unclassified (9a–9c), mode
10 once per directory that classification excludes (10a–10c), mode 12 once per kind of executable
artifact that is not Lean (12a–12c), mode 15 once per step field that changes whether a step runs
(15a–15c), mode 16 once per way of changing the job or the workflow above the step level
(16a–16d), mode 19 once per form of malformed YAML the reader claims to refuse (19a–19c), and
mode 20 once per document that must carry the canonical scope sentence (20a–20c). Each run must make the pipeline exit nonzero **and must be caught by the layer
responsible for it** — a fixture that failed for some unrelated reason would satisfy "exits
nonzero" and prove nothing.

**The gate is a stage, not an assumption.** Every other stage runs a check directly, but the thing
these documents call the pipeline is the shell script that wraps them. A wrapper that stopped
propagating an exit status — a dropped `$?`, a stray `|| true`, a reordered branch — would leave
every individual stage reporting exactly what it reports today while CI went green on a corrupted
tree, and CI alone would never notice, because it only ever runs the gate on a healthy tree. So
each fixture also runs `./scripts/check_axioms.sh` on its corrupted copy and requires both a
nonzero status and the diagnostic naming the failing layer. Fixture 6b is the one that requires
the gate to *pass*: only the hash manifest is stale there, and the manifest is CI's own step
rather than part of the gate.

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
 fixture     layer     build   imports    policy     audit      gate  manifest      docs
       1   imports         0         1         0         0         1         0         -   ok
       2    policy         0         0         1         0         1         0         -   ok
       3    policy         0         0         1         0         1         0         -   ok
       4     build         1         0         1         -         1         0         -   ok
       5     audit         0         0         0         1         1         0         -   ok
       6  manifest         0         1         0         0         1         1         -   ok
      6b  manifest         0         0         0         0         0         1         -   ok
      7a    policy         0         0         1         0         1         0         -   ok
      7b    policy         0         0         1         0         1         0         -   ok
      7c    policy         0         0         1         0         1         0         -   ok
      7d    policy         0         0         1         0         1         0         -   ok
       8  manifest         0         0         0         0         0         1         -   ok
      9a   imports         0         1         0         0         1         0         -   ok
      9b   imports         0         1         0         0         1         0         -   ok
      9c   imports         0         1         0         0         1         1         -   ok
     10a   imports         0         1         0         0         1         0         -   ok
     10b   imports         0         1         0         0         1         0         -   ok
     10c   imports         0         1         0         0         1         0         -   ok
     12a   imports         0         1         0         0         1         0         -   ok
     12b   imports         0         1         0         0         1         0         -   ok
     12c   imports         0         1         0         0         1         0         -   ok
     15a      docs         -         0         0         -         -         0         1   ok
     15b      docs         -         0         0         -         -         0         1   ok
     15c      docs         -         0         0         -         -         0         1   ok
     16a      docs         -         0         0         -         -         0         1   ok
     16b      docs         -         0         0         -         -         0         1   ok
     16c      docs         -         0         0         -         -         0         1   ok
     16d      docs         -         0         0         -         -         0         1   ok
      17      docs         -         0         0         -         -         0         1   ok
      18     audit         0         0         0         1         1         0         -   ok
     19a      docs         -         0         0         -         -         0         1   ok
     19b      docs         -         0         0         -         -         0         1   ok
     19c      docs         -         0         0         -         -         0         1   ok
     20a      docs         -         0         0         -         -         0         1   ok
     20b      docs         -         0         0         -         -         0         1   ok
     20c      docs         -         0         0         -         -         0         1   ok
      14   imports         0         1         0         0         1         0         -   ok
      11      docs         -         0         0         -         -         0         1   ok

all 38 fixture run(s) covering 19 failure mode(s) behaved as declared: each broke the pipeline, and each was caught by the layer named for it. Working tree unchanged (28 file(s) hashed before and after, excluding .git/, .lake/, __pycache__/).
```

| # | Fragment | Layer under test | Why that layer, and why not another |
|---|---|---|---|
| 1 | `AhlProofs/Extra.lean`, containing `axiom planted_bad : False`, never added to `AhlProofs.lean` | import invariant | The build and the environment audit are blind here by construction: an unimported file is never compiled, so no constant of it exists to audit. This is the ordinary case of forgetting an `import` line, and it produces a repository whose green CI says nothing at all about that file. |
| 2 | `set_option warningAsError false in` / `example : False := <placeholder>` | source policy | The environment audit cannot see this: an `example` is elaborated and discarded, never stored in `env.constants`, and the local `set_option` removes the build failure Lean's own warning would otherwise cause. |
| 3 | `set_option debug.skipKernelTC true in` + a `run_tac` proof assigning `True.intro` to a goal of `False` | source policy | Lean 4.31.0 accepts this with exit 0 and a **clean** axiom closure — no placeholder axiom, no axiom of our own — because the kernel never re-checked the term. No walk over `env.constants` can detect it; only refusing the lexeme can. |
| 4 | `theorem probe_incomplete : True := by <placeholder>` | `lake build` | `declaration uses 'sorry'` is a warning promoted to an error by `lakefile.toml`. The source policy also rejects the lexeme (the runner asserts both), and the environment audit would have found `sorryAx` in the constant's closure had the build been allowed to finish — hence `-` for the audit stage: with no `.olean`s, its exit status would say nothing about the audit. |
| 5 | `axiom probe_axiom : False` | environment audit | Both of the audit's own-axiom findings fire: `own axiom declaration(s), not part of Lean's trusted kernel` and `axiom closure is not a subset of the allowed set`. Declaring an axiom is not a Lean warning, so the build is untroubled by it. |
| 6 | A new `.lean` file under `AhlProofs/`, manifest left stale | hash manifest | In this plain form the import invariant fires too; the runner still requires the *manifest* check to fail, so the fixture cannot pass on the strength of another layer. |
| 6b | The same file, with its `import` line added | hash manifest | The import invariant now passes, leaving the manifest check as the only thing between the tree and a green run. This is what establishes that the two layers are independent rather than one masking the other, and it is the one run where `./scripts/check_axioms.sh` is required to *succeed*. |
| 7a | `-- sorry` in a Lean line comment | source policy | One run per forbidden lexeme, each asserting that lexeme's own finding message. A comment reaches no elaborator, so the build still succeeds and the audit still finds nothing: the policy is the only thing that can fail, which is what isolates the rule. It also exercises the property the policy claims — that the ban is total, comments included. |
| 7b | `-- admit` in a Lean line comment | source policy | The rule that had no fixture at all until this one. Deleting the `admit` pattern from `scripts/check_source_policy.py` used to leave the whole suite green; it now fails this run. |
| 7c | `-- warningAsError false` in a Lean line comment | source policy | Fixture 2 exercises this lexeme in its natural setting; this run pins the rule itself, independent of whether an `example` or a `set_option` happens to be involved. |
| 7d | `-- debug.skipKernelTC` in a Lean line comment | source policy | Same, for the kernel-typecheck escape: the rule is tested apart from the elaborate proof that motivates it. |
| 8 | `scripts/nested/helper.py` and `helper.sh`, manifest left stale | hash manifest | The manifest documents itself as hashing *every* audit script, but discovered them with a single-level `glob` while the library used `rglob` — so a script one directory down was outside the manifest while the prose said it was covered. The fixture requires the staleness report to name both nested paths, so the recursive walk is exercised for more than whichever extension a single file would have picked. Like 6b, the gate itself passes: nothing the gate covers is broken. |
| 9a | `Foo.lean` in the repository root, containing `axiom planted_at_root : False` | Lean-file coverage | The case that passed everything: not under `AhlProofs/` so no import invariant looked at it, not under `AhlProofs/` or `scripts/` so the manifest did not hash it, no forbidden lexeme so the policy passed it, not in the build target so `lake build` ignored it, never elaborated so the audit never saw the axiom. Every check walked a chosen directory; none asked whether this file had a home. |
| 9b | `docs/Notes.lean` | Lean-file coverage | The same failure in a different directory, which is the point: the rule is now "every `.lean` must be classified", not "these directories are walked", so `docs/` needs no special case and neither will the next directory someone creates. |
| 9c | `scripts/nested/Helper.lean` | Lean-file coverage | Under `scripts/`, where the manifest *does* see it (fixture 8's recursive walk) but where nothing classified it. The manifest goes stale here too, and the fixture asserts both — the coverage rule is what names it, the manifest is what would have noticed the bytes. |
| 10a | `.git/Bad.lean` | Lean-file coverage | The same class again, arriving through an *exclusion* rather than an omission: classification skipped `.git`, `.lake` and `__pycache__`, so a file there was neither classified nor refused while layer 1 printed "0 unclassified". A `.lean` under any of the three is now refused outright — none of them holds a Lean source in this project, so there is no case to distinguish. |
| 10b | `.lake/Bad.lean` | Lean-file coverage | Lake's build output. This repository takes no dependencies, so Lake never places sources there; a `.lean` under it is a mistake or a hiding place. |
| 10c | `__pycache__/Bad.lean` | Lean-file coverage | Python bytecode caches. Same reasoning, and the directory this was first demonstrated in. |
| 12a | `tools/helper.py` | covered-artifact coverage | The class again, one file type over. The `.lean` rule said nothing about `.py`, so a Python file outside `scripts/` was hashed by nothing and classified by nobody; a workflow step invoking it would have run unhashed content, and the command-set comparison would have noticed the new *call* while saying nothing about the *callee* being outside the manifest. |
| 12b | `tools/helper.sh` | covered-artifact coverage | Same, for shell. Both categories now require the file to live under `scripts/` **and** to be present in `reports/PROOF.sha256`, with the manifest asked for its own file list rather than the rule restating it. |
| 12c | `.github/workflows/extra.yml` | covered-artifact coverage | The sharpest of the three: GitHub Actions runs every file under `.github/workflows/` on its own schedule and permissions, with no step of this repository referring to it. So YAML is declared file by file, not admitted by directory, and each declared file must also be hashed. |
| 15a | `if: false` on the regression-fixtures step | document claims | The worst hole found in twelve rounds: with the manifest regenerated as any author would, CI went green having never run a fixture. The label check saw the step in place, the command comparison saw the same commands, and that the step would not run was visible to nothing. The step schema now admits `name` plus exactly one of `run` or a SHA-pinned `uses`, and refuses everything else. |
| 15b | `continue-on-error: true` on the proof gate | document claims | The same, one field over: the gate would run, fail, and not fail the job. |
| 15c | `shell: bash` on a step | document claims | Harmless in itself, and refused anyway — the schema does not enumerate the dangerous fields, it admits only the two this workflow uses, so a field GitHub adds tomorrow is refused before anyone has to think about what it means. |
| 16a | `if: false` beside `runs-on:` | document claims | The step schema was closed at the wrong depth. Disabling the *job* leaves every step-level check reporting that the steps are exactly right, and CI goes green having run nothing at all. |
| 16b | `continue-on-error: true` as a job key | document claims | The same at job level: everything runs, nothing fails the job. |
| 16c | `permissions: write-all` as a top-level key | document claims | The workflow's own level was unguarded too. Admitted keys are `name`, `on`, `jobs`; anything else is refused before someone has to decide what it means. |
| 16d | `runs-on: self-hosted` | document claims | The image is not pinned by digest and is trusted unverified — the schema does not fix that and does not pretend to. What it does is make a change visible: swapping the runner changes everything this repository says about reproducibility. |
| 17 | `uses: evil/checkout@0000…0000` — a well-formed pin to another repository | document claims | The schema checked the *form* of a pin, not which action it names. The step keeps its name, so the label check is satisfied; the action runs before every check in the job and can replace the working tree wholesale, after which everything downstream verifies whatever it left behind. The admitted `uses` values are now exact. |
| 18 | `axiom smuggled_in_audit : False` in `scripts/Audit.lean`, ahead of the audit's own `#eval` | environment audit | The audit filtered by *home module*, and a constant declared in the file being elaborated has no home module — so an axiom there passed the audit, passed the source policy (`axiom` is not one of its four lexemes) and passed the gate, while the documents said "no `axiom` declaration of our own". |
| 19a | a duplicate top-level key in `ci.yml` | document claims | A reader that calls itself fail-closed accepted duplicates and silently kept the last: the first was simply lost. |
| 19b | a duplicate `run:` on a step | document claims | The same at step level. |
| 19c | a tab in place of indentation | document claims | This reader measures indentation in spaces; a tab would be read at the wrong depth. The file is refused rather than guessed at. |
| 20a | the canonical scope sentence removed from `README.md` | document claims | The sentence naming the boundary — order and identity of the steps checked, contents not — is required verbatim in all three documents, because the boundary was once stated only in `reports/PROOF.md` while the other two went on promising "the same procedure". One run per document: the requirement is one claim entry per document, and a single run would leave two of them unexercised. |
| 20b | the same, from `reports/PROOF.md` | document claims | |
| 20c | the same, from `reports/TOOLCHAIN.md` | document claims | |
| 14 | `lake-manifest.json` removed from `FIXED_FILES` in `scripts/gen_proof_sha256.py` | covered-artifact coverage | That file carries none of the covered suffixes, so the suffix rule says nothing about it, and the only thing that used to protect it was a list inside the very script an edit would touch — dropping the entry produced a shorter manifest and a green run. `scripts/check_imports.py` now declares the build and pin files separately and requires the two lists to be equal. |
| 11 | An extra `FreeBSD/x86_64)` branch in the published install script, selecting the Linux archive | document claims | Every required branch and the `*)` default remain, and the set of archives offered is unchanged — which is why the previous version of the platform check passed it. It asked whether the recorded platforms were covered, not whether anything else was, so a platform quietly stopped being refused and started receiving another platform's build. The branch set must now equal the declared one exactly. This is the one fixture whose subject lives in a document rather than in the sources, so it is also the only one that runs `scripts/check_doc_claims.py`. |

For every fixture except 6 and 6b the runner regenerates the manifest inside the copy after
applying the fixture, so manifest staleness cannot be what fails and the named layer is
demonstrably the one doing the work. Fixtures 6 and 6b leave it stale, because there staleness is
the subject.

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
== layer 1/3: scripts/check_imports.py (artifact coverage & import invariant) ==
every covered artifact accounted for: 9 library module(s) under AhlProofs/, all reachable from AhlProofs.lean (10 module(s) in the closure); 1 declared auxiliary .lean; 7 tooling file(s) under scripts/; 1 declared CI configuration file(s); 0 unclassified, all hashed

== layer 2/3: scripts/check_source_policy.py (policy over source text) ==
source policy holds: 11 .lean file(s) scanned, none contains `sorry`, `admit`, `warningAsError false`, `debug.skipKernelTC`

== layer 3/3: scripts/Audit.lean (environment-based axiom & placeholder-proof audit) ==
scanned 645 constant(s) whose home module is `AhlProofs` or under it (every kind of declaration, not a curated subset of theorems)
own axiom declarations: (none)
sorryAx present in the closure of: (none)
Classical.choice used by: #[AhlProofs.commit_plain_descriptor_collision]
axiom(s) outside the allowed set [propext, Classical.choice, Quot.sound]: (none)
axiom(s) declared by this audit file itself: (none)
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

**The whole procedure is one script.** `reports/TOOLCHAIN.md`'s "Install" section is a single
runnable file that installs the pinned toolchain and runs every check below, working through the
steps of the `lean` job of `.github/workflows/ci.yml` in that job's order, with each block
labelled by the CI step it corresponds to. Those labels are checked against the workflow; what
each block runs is not (see "What is checked about this document", item 5). Running that file is
the recommended way to reproduce this, and it is the closest thing to a CI run that this
repository can offer a reader — not a verified equivalent of one.

The commands below are what it runs **after** the toolchain is verified. They are a subset, and
deliberately named as one: the script additionally runs `scripts/check_imports.py` and
`scripts/check_source_policy.py` on their own, and cross-checks `lean-toolchain` against the
pinned release, all *before* fetching the archive — as CI does. Run only these five with a
toolchain already on `PATH` and the import invariant and the source policy are still covered, but
by `./scripts/check_axioms.sh` at the end rather than up front, and the pin cross-check is not
covered at all. From a clean clone:

```sh
git clone https://github.com/evidentum-io/ahl-proofs.git
cd ahl-proofs
python3 scripts/gen_proof_sha256.py --check
lake clean && time lake build
python3 scripts/regression_fixtures.py
./scripts/check_axioms.sh
python3 scripts/check_doc_claims.py
```

`scripts/regression_fixtures.py` is much the slowest of the five — it builds the library once per
fixture run, in a throwaway copy — and it is the one that checks the checks; running it last,
after the gate, works equally well, since it does not touch the working tree either way.
`scripts/check_doc_claims.py` rebuilds once more, to check the published build transcript, and so
leaves a fresh build behind it.

`.github/workflows/ci.yml` is the authority on the exact commands CI runs, on every push (any
branch) and every pull request; read it alongside "Trust boundary" above, which says what a
passing run of all of this does and does not mean.
