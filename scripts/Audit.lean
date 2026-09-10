import AhlProofs
import Lean

/-!
# Environment-based axiom & placeholder-proof audit

Replaces the earlier text-based audit (`list_theorems.py` + `check_axiom_output.py`), which
discovered its audit targets by regex-parsing the `.lean` source files. That approach had two
proven blind spots, both confirmed by a passing build that the old audit did not catch:

1. **Visibility modifiers.** The old target regex only matched a line beginning with the bare
   keyword `axiom`. `private axiom foo : False` was invisible to it, and so was any declaration
   whose keyword the regex did not special-case (e.g. `example`, which never appeared in its
   target list at all).
2. **Comments vs. string literals.** The old comment-stripper did not know about string
   literals, so a string containing the two characters `/-` (anywhere, including a definition's
   own name is irrelevant — only the *content* of a string literal matters) caused it to treat
   everything up to the next `-/`-looking substring as a comment, silently deleting whatever
   declarations sat inside. Separately, its search for Lean's placeholder proof term matched that
   word on a word boundary, which does not match `sorryAx`, the constant the placeholder actually
   elaborates to.

Both classes are closed *constructively* here, not by enumerating known cases: this file audits
the **compiled `Lean.Environment`** produced by `import AhlProofs`, not the source text. The
environment is Lean's own authoritative record of every declaration that exists after
elaboration — there is no text to mis-parse, no comment syntax to get wrong, and no keyword
spelling to miss, because visibility modifiers and `example` all still produce (or, for
`example`, at least type-check against) real entries in `env.constants`.

## What is checked, over *every* constant whose home module is under `AhlProofs.*`

(not just `theorem`/`lemma` — `def`, `instance`, `private` declarations, automatically generated
auxiliary lemmas, everything; see `isLibraryConst` below)

* **No axiom declared by this repository.** Any `ConstantInfo.axiomInfo` found in an `AhlProofs.*`
  module is, by construction, one of ours — the trusted kernel axioms (`propext`,
  `Classical.choice`, `Quot.sound`) live in `Init`/`Lean` modules, never here.
* **No axiom outside the allowed set** in the transitive closure of any constant, computed by
  `Lean.collectAxioms` (the same primitive `#print axioms` itself uses). This subsumes the
  placeholder-proof check: Lean's placeholder proof term elaborates to the axiom `sorryAx`
  (`Init/Prelude.lean`), which is therefore just another name that must be in the allowed set —
  and it is not, so a placeholder anywhere in the transitive closure of any constant is caught by
  exactly the same check that catches a stray `axiom`, with no separate word-boundary text search
  required.
* **The `priority-zero.md` claim**: the set of constants whose closure contains
  `Classical.choice` is *exactly* `{AhlProofs.commit_plain_descriptor_collision}` — checked
  against every one of the (currently 645) constants under `AhlProofs.*`, not only the 102
  named `theorem`/`lemma` declarations, and it still holds exactly at that finer grain: no
  automatically generated helper (structural recursion, decidability instances, `_proof_i`
  obligations, ...) anywhere in the library pulls in choice by accident.

## Why `Lean.collectAxioms` rather than shelling out to `#print axioms` per name

`#print axioms <name>` is a command whose output is printed as human-readable *text* that then
has to be parsed back into structured data (this is exactly what the old `check_axiom_output.py`
did, matching printed lines against a name list built by `list_theorems.py` — two independent
places the pipeline could go wrong). `Lean.collectAxioms` is the function `#print axioms` calls
internally; calling it directly here, once per constant, from inside the same elaboration that
already has the environment loaded, removes both the shelling-out and the text-format parsing.

## Why this needs no target list at all

`list_theorems.py` had to *discover* what to audit before auditing it, and both blind spots above
are exactly discovery failures. This file has no discovery step: `for (name, info) in
env.constants` after `import AhlProofs` walks the constant table Lean itself built while
elaborating every module of the library. A declaration that failed to reach `env.constants` would
also have failed to build — the target list and the build are the same event, not two things that
can drift apart.

## What this file does *not* cover, and which sibling layer does

This audit sees exactly what was compiled, which is exactly what the root module `AhlProofs.lean`
transitively imports. Two gaps follow, and neither is closed here:

* A `.lean` file under `AhlProofs/` that nobody imports is never built, so no constant of its
  reaches `env.constants` and this audit is silent about it. `scripts/check_imports.py` closes
  that by requiring every file found on disk to be reachable by imports from the root module.
* A declaration that never becomes a constant (`example`), and a declaration whose kernel
  typecheck was locally disabled (its axiom closure is clean because nothing was checked), are
  both invisible to a walk over `env.constants` and `Lean.collectAxioms`.
  `scripts/check_source_policy.py` refuses the four lexemes that make either possible. That
  layer is a policy over source text, not a semantic check: it establishes nothing about meaning
  and does not replace this file.

`scripts/check_axioms.sh` runs all three in order. What none of them defends against is a
participant with write access editing the checks themselves — see "Trust boundary" in
`reports/PROOF.md`.
-/

open Lean

/-- The outermost component of a (possibly dotted) name, read root-first: for example
`AhlProofs.Closure.Model` ↦ `` `AhlProofs``, and `_private.AhlProofs.Model.0.sample_a`
↦ `` `_private``. Private declarations are renamed by the elaborator to sit under `_private`
regardless of the namespace they were written in (confirmed empirically: a `private axiom` in
`AhlProofs/Model.lean` is stored as `_private.AhlProofs.Model.0.<name>`) — filtering by *name*
prefix would therefore miss exactly the declarations this audit exists to catch. Filtering by the
constant's *home module* instead (see `isLibraryConst`) is unaffected by name-mangling of any
kind. -/
partial def rootComponent : Name → Name
  | .str .anonymous s => .str .anonymous s
  | .num .anonymous n => .num .anonymous n
  | .str p _ => rootComponent p
  | .num p _ => rootComponent p
  | n => n

/-- The library's own root module component. Every module this project builds is named
`AhlProofs` or `AhlProofs.<something>`. -/
def libraryRootModule : Name := `AhlProofs

/-- The module `name` was compiled into, or `none` if `name` was declared in the file currently
being elaborated (this file declares no constants of its own besides the definitions here, none
of which are under `AhlProofs`, so this case never contributes a false positive or a silent
omission). -/
def constModule (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx]?

/-- Whether `name` is a constant this repository — as opposed to `Init`, `Lean`, or anything
else on the search path — is responsible for. -/
def isLibraryConst (env : Environment) (name : Name) : Bool :=
  match constModule env name with
  | some m => rootComponent m == libraryRootModule
  | none => false

/-- The only axioms this repository accepts anywhere in any constant's transitive closure:
propositional extensionality, choice, and quotient soundness — Lean's own standard trusted
kernel trio, no more. `sorryAx` is deliberately not in this list: it is the axiom Lean's
placeholder proof term elaborates to (`Init/Prelude.lean`), so a placeholder anywhere in a
closure is caught here as "an axiom outside the allowed set" without a separate text search. -/
def allowedAxioms : List Name := [`propext, `Classical.choice, `Quot.sound]

/-- The `ahl/docs-md/priority-zero.md` claim — paraphrased rather than quoted, because this file
is itself subject to `scripts/check_source_policy.py` and may not spell the forbidden lexemes even
in prose: no placeholder proof and no axiom of this repository's own, and `Classical.choice` only
in `commit_plain_descriptor_collision`. Checked here against every constant under `AhlProofs.*`,
not a hand-picked list of "the interesting theorems" — see the module docstring. -/
def expectedChoiceUsers : List Name := [`AhlProofs.commit_plain_descriptor_collision]

#eval show MetaM Unit from do
  let env ← getEnv
  let mut scanned : Nat := 0
  let mut ownAxioms : Array Name := #[]
  let mut outsideAllowed : Array (Name × Name) := #[]
  let mut sorryUsers : Array Name := #[]
  let mut choiceUsers : Array Name := #[]
  for (name, info) in env.constants do
    if isLibraryConst env name then
      scanned := scanned + 1
      if let .axiomInfo _ := info then
        ownAxioms := ownAxioms.push name
      let axs ← Lean.collectAxioms name
      for ax in axs do
        if ax == `sorryAx then
          sorryUsers := sorryUsers.push name
        if ax == `Classical.choice then
          choiceUsers := choiceUsers.push name
        if !allowedAxioms.contains ax then
          outsideAllowed := outsideAllowed.push (name, ax)

  IO.println s!"scanned {scanned} constant(s) whose home module is `AhlProofs` or under it \
(every kind of declaration, not a curated subset of theorems)"
  IO.println s!"own axiom declarations: {if ownAxioms.isEmpty then "(none)" else toString ownAxioms}"
  IO.println s!"sorryAx present in the closure of: \
{if sorryUsers.isEmpty then "(none)" else toString sorryUsers}"
  IO.println s!"Classical.choice used by: {choiceUsers}"
  IO.println s!"axiom(s) outside the allowed set {allowedAxioms}: \
{if outsideAllowed.isEmpty then "(none)" else toString outsideAllowed}"

  let mut problems : Array String := #[]
  if scanned == 0 then
    problems := problems.push
      "zero constants scanned under AhlProofs — refusing to report success on nothing audited"
  if !ownAxioms.isEmpty then
    problems := problems.push
      s!"own axiom declaration(s), not part of Lean's trusted kernel: {ownAxioms}"
  if !outsideAllowed.isEmpty then
    problems := problems.push
      s!"constant(s) whose axiom closure is not a subset of the allowed set \
{allowedAxioms}: {outsideAllowed}"
  let choiceSorted := choiceUsers.toList.eraseDups
  if choiceSorted != expectedChoiceUsers then
    problems := problems.push
      s!"Classical.choice usage does not match ahl/docs-md/priority-zero.md's claim \
(expected exactly {expectedChoiceUsers}, got {choiceSorted})"

  if problems.size > 0 then
    let report := "\n  - " ++ String.intercalate "\n  - " problems.toList
    throwError s!"AUDIT FAILED — reasons:{report}"

  IO.println "extra axioms: (none) PASS"
