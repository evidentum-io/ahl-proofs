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
elaborating every module of the library. Every *persistent* declaration of a built module is
there — `theorem`, `def`, `instance`, `private`, generated helpers alike — so for those the target
list and the build are the same event and cannot drift apart.

The exception is worth naming rather than glossing: a declaration that stores no constant is not
here either. `example` is elaborated and discarded, so it never reaches `env.constants` and this
audit is silent about it — which is not a build failure, it is a successful build of a thing the
audit cannot see. That gap is covered by `scripts/check_source_policy.py`, which refuses the
lexemes an `example` would have to carry to be dangerous, and by regression fixture 2.

## Why the audit re-asks the kernel instead of trusting that the build checked

Everything above reads the environment the build produced. That is authoritative about *what
declarations exist* and *which axioms they reach*, but it is not by itself evidence that any of
them was ever type-checked: Lean has an option that switches the kernel's re-typechecking off for
the declarations under it, and a declaration accepted that way sits in `env.constants` looking
exactly like a checked one — its axiom closure is empty because nothing was checked. Until now the
only defence was `scripts/check_source_policy.py` refusing that option's name in the source text,
which is a defence against a *spelling*: Lean accepts the same option under a French-quoted
identifier, and the byte pattern did not match it. A theorem of `False` written that way passed the
build, the policy and the whole gate.

So this file stops inferring that the kernel ran and makes it run, here, under options it
constructs itself:

* `env.toKernelEnv` exposes the kernel-level environment behind the elaborated one.
* Every constant this repository owns is re-added to a copy of it under a fresh name, via
  `Kernel.Environment.addDecl`, with an **empty option set** built in this file (`recheckOptions`).
  `addDecl` type-checks the declaration's value against its type unless told not to, and what it
  is told comes from this audit, never from the source being audited. A `set_option` in a proof
  file — under any spelling, quoted or not — cannot reach it.
* Re-adding under a fresh name is what makes this a check of each constant *individually*. A
  declaration that was smuggled in unchecked still sits in the environment, so its dependents
  re-check fine against its stated type; but the smuggled declaration is itself in the list, and
  its own re-add is what fails.

Constants are re-added by kind: theorems, safe definitions, opaque definitions and axioms one at a
time; inductive types as whole families (`Declaration.inductDecl`, with the family's internal
references rewritten to the fresh copies), which makes the kernel re-derive and re-check their
constructors and recursors as well.

The one kind not re-added is an unsafe or `partial` constant — in this library, only the compiler
companions Lean generates for `partial` definitions. Nothing that carries proof content can rest on
them, and that is not an assertion made here: every declaration re-added above is a *safe* one, and
the kernel refuses a safe declaration that mentions a `partial` one ("safe declaration must not
contain partial declaration '...'"). Each successful re-add is therefore itself evidence that the
constant does not depend on anything skipped. Any *other* reason for skipping a constant is a
failure, not a silent omission: the classification is exhaustive, its default branch fails, and the
buckets are required to add up to the number of constants scanned.

## What this file does *not* cover, and which sibling layer does

This audit sees exactly what was compiled, which is exactly what the root module `AhlProofs.lean`
transitively imports. Two gaps follow, and neither is closed here:

* A `.lean` file under `AhlProofs/` that nobody imports is never built, so no constant of its
  reaches `env.constants` and this audit is silent about it. `scripts/check_imports.py` closes
  that by requiring every file found on disk to be reachable by imports from the root module.
* A declaration that never becomes a constant (`example`) is invisible to a walk over
  `env.constants` and `Lean.collectAxioms`, and stays invisible to the kernel re-check too — there
  is no constant to re-add. `scripts/check_source_policy.py` refuses the lexemes an `example` would
  have to carry to be dangerous. That layer is a policy over source text, not a semantic check: it
  establishes nothing about meaning and does not replace this file. The sibling gap — a
  declaration whose kernel typecheck was locally switched off — used to belong to that same policy
  layer and no longer does: it is closed here, constructively, by the re-check described above.

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

/-- Whether `name` was declared in the file currently being elaborated — that is, in **this**
file — rather than imported from a module.

This exists because the audit had a blind spot exactly where it was least expected: itself.
`isLibraryConst` filters by home module, and a constant declared here has no home module at all,
so `axiom smuggled_in_audit : False` appended to this file passed the audit, passed the source
policy (`axiom` is not one of its four lexemes) and passed the whole gate. Such an axiom cannot
make any AhlProofs theorem depend on it — nothing imports this file, and `collectAxioms` over the
library would not reach it — so no proof was ever at risk. What was at risk was the sentence:
`README.md` says "No `axiom` declaration of our own", and until now that was true of the library
and unchecked of the tool that certifies it.

The boundary is exact and is stated wherever the claim is made: `#eval` runs where it stands, so
this reports axioms declared **ahead of** the evaluation below. One appended after it is inert —
nothing imports this file and the audit has already run — and is not reported. -/
def declaredInThisFile (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).isNone

/-- The options the kernel re-check runs under: empty, so every option has its default value —
including the one whose default is "do type-check". This value is built here, in the audit, and
handed to `Kernel.Environment.addDecl` explicitly, so no `set_option` in an audited source file can
influence it under any spelling. -/
def recheckOptions : Options := {}

/-- The fresh name a constant is re-added under, so re-adding it cannot collide with the constant
already present. The suffix is deliberately not a legal source identifier suffix anyone would
write. -/
def recheckName (n : Name) : Name := n ++ `_ahlKernelRecheck

/-- Rewrite constant references according to `m`. Needed when re-adding an inductive family: the
family's types and constructors refer to one another, and in the copy those references must point
at the copies, not back at the originals. -/
def renameConstants (m : Std.HashMap Name Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => (m[n]?).map (fun n' => .const n' us)
    | _ => none

/-- The single reason a constant of this library may be left out of the kernel re-check. Written
once and compared against, so that a constant skipped for any other reason fails the audit instead
of quietly reducing what was checked. -/
def unsafeCompanionReason : String :=
  "unsafe/`partial` constant — in this library, only a compiler companion Lean generates for a \
`partial` definition"

/-- The exhaustive list of accepted skip reasons. Anything else is an audit failure. -/
def declaredSkipReasons : List String := [unsafeCompanionReason]

#eval show MetaM Unit from do
  let env ← getEnv
  let mut scanned : Nat := 0
  let mut ownAxioms : Array Name := #[]
  let mut outsideAllowed : Array (Name × Name) := #[]
  let mut sorryUsers : Array Name := #[]
  let mut choiceUsers : Array Name := #[]
  let mut auditOwnAxioms : Array Name := #[]
  for (name, info) in env.constants do
    if declaredInThisFile env name then
      if let .axiomInfo _ := info then
        auditOwnAxioms := auditOwnAxioms.push name
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

  -- Kernel re-check. Classify every constant this repository owns into "re-add it directly",
  -- "re-add it as part of its inductive family", or "skipped, for a reason that must be on the
  -- declared list". The default branch is a failure, so a constant kind this audit has never seen
  -- cannot pass by falling through.
  let mut singles : Array (Name × Declaration) := #[]
  let mut families : Std.HashMap Name (List Name) := {}
  let mut inductCount : Nat := 0
  let mut ctorCount : Nat := 0
  let mut recCount : Nat := 0
  let mut skippedList : Array (Name × String) := #[]
  for (name, info) in env.constants do
    if isLibraryConst env name then
      let fresh := recheckName name
      match info with
      | .thmInfo v => singles := singles.push (name, .thmDecl { v with name := fresh })
      | .opaqueInfo v =>
          if v.isUnsafe then skippedList := skippedList.push (name, unsafeCompanionReason)
          else singles := singles.push (name, .opaqueDecl { v with name := fresh })
      | .axiomInfo v =>
          if v.isUnsafe then skippedList := skippedList.push (name, unsafeCompanionReason)
          else singles := singles.push (name, .axiomDecl { v with name := fresh })
      | .defnInfo v =>
          if v.safety == .safe then
            singles := singles.push (name, .defnDecl { v with name := fresh })
          else
            skippedList := skippedList.push (name, unsafeCompanionReason)
      | .inductInfo v =>
          inductCount := inductCount + 1
          families := families.insert v.all.head! v.all
      | .ctorInfo _ => ctorCount := ctorCount + 1
      | .recInfo _ => recCount := recCount + 1
      | _ => skippedList := skippedList.push (name, "unhandled constant kind")

  -- Note on what the skip costs, and why no separate reachability scan is needed: every
  -- declaration re-added below is a *safe* one, and Lean's kernel refuses a safe declaration that
  -- mentions an unsafe or `partial` constant ("safe declaration must not contain partial
  -- declaration '...'", verified against this very library's `._unsafe_rec` companions). So each
  -- successful re-add is itself evidence that the constant does not rest on anything skipped
  -- here; an earlier version of this audit walked every value to establish the same fact by hand,
  -- at four times the cost of the re-check it was guarding.
  let kenv := env.toKernelEnv
  let mut rejected : Array Name := #[]
  let mut recheckedSingles : Nat := 0
  for (name, decl) in singles do
    match kenv.addDecl recheckOptions decl with
    | .ok _ => recheckedSingles := recheckedSingles + 1
    | .error _ => rejected := rejected.push name

  let mut recheckedFamilies : Nat := 0
  let mut missingCtors : Array Name := #[]
  let mut unsafeFamilies : Array Name := #[]
  for (head, all) in families.toList do
    let mut ren : Std.HashMap Name Name := {}
    for n in all do
      ren := ren.insert n (recheckName n)
      if let some (.inductInfo v) := env.find? n then
        for c in v.ctors do ren := ren.insert c (recheckName c)
    let mut types : List InductiveType := []
    let mut lparams : List Name := []
    let mut nparams : Nat := 0
    let mut famUnsafe : Bool := false
    for n in all do
      if let some (.inductInfo v) := env.find? n then
        lparams := v.levelParams
        nparams := v.numParams
        famUnsafe := v.isUnsafe
        let mut ctors : List Constructor := []
        for c in v.ctors do
          match env.find? c with
          | some (.ctorInfo cv) =>
              ctors := ctors ++ [{ name := recheckName c, type := renameConstants ren cv.type }]
          | _ => missingCtors := missingCtors.push c
        types := types ++ [{ name := recheckName n, type := renameConstants ren v.type, ctors }]
    if famUnsafe then
      unsafeFamilies := unsafeFamilies.push head
    else
      match kenv.addDecl recheckOptions (.inductDecl lparams nparams types false) with
      | .ok _ => recheckedFamilies := recheckedFamilies + 1
      | .error _ => rejected := rejected.push head

  let undeclaredSkips := skippedList.filter (fun (_, why) => !declaredSkipReasons.contains why)
  let accounted := recheckedSingles + rejected.size + skippedList.size + inductCount
    + ctorCount + recCount

  IO.println s!"scanned {scanned} constant(s) whose home module is `AhlProofs` or under it \
(every kind of declaration, not a curated subset of theorems)"
  IO.println s!"own axiom declarations: {if ownAxioms.isEmpty then "(none)" else toString ownAxioms}"
  IO.println s!"sorryAx present in the closure of: \
{if sorryUsers.isEmpty then "(none)" else toString sorryUsers}"
  IO.println s!"Classical.choice used by: {choiceUsers}"
  IO.println s!"axiom(s) outside the allowed set {allowedAxioms}: \
{if outsideAllowed.isEmpty then "(none)" else toString outsideAllowed}"
  IO.println s!"axiom(s) declared by this audit file ahead of this check: \
{if auditOwnAxioms.isEmpty then "(none)" else toString auditOwnAxioms}"
  IO.println s!"kernel re-check: re-added {recheckedSingles} of {singles.size} constant(s) \
individually and {recheckedFamilies} of {families.size} inductive family(ies) — the families \
carry {inductCount} type(s), {ctorCount} constructor(s) and {recCount} recursor(s) — into a \
kernel environment holding this audit's own empty option set"
  IO.println s!"rejected by the kernel on re-check: \
{if rejected.isEmpty then "(none)" else toString rejected}"
  IO.println s!"not re-added: {skippedList.size} constant(s), \
{if undeclaredSkips.isEmpty then "each for a declared reason" else "SOME FOR AN UNDECLARED REASON"} \
(no safe declaration may mention one — the kernel refuses that, so every re-add above is also \
evidence that nothing checked rests on them); \
{accounted} of {scanned} scanned constant(s) accounted for"

  let mut problems : Array String := #[]
  if scanned == 0 then
    problems := problems.push
      "zero constants scanned under AhlProofs — refusing to report success on nothing audited"
  if !auditOwnAxioms.isEmpty then
    problems := problems.push
      s!"this audit file declares axiom(s) of its own: {auditOwnAxioms}. They cannot affect any \
AhlProofs theorem — nothing imports this file, and the library's axiom claim is about \
`AhlProofs` — but a tool that certifies the absence of axioms should not smuggle one, and this \
is reported for every axiom declared ahead of the evaluation below."
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
  if !rejected.isEmpty then
    problems := problems.push
      s!"the kernel rejected {rejected.size} constant(s) when asked to check them again under \
this audit's own options: {rejected}. A constant that the build accepted but the kernel refuses \
was not type-checked when it was added."
  if recheckedSingles == 0 then
    problems := problems.push
      "the kernel re-check re-added no constant at all — refusing to report success on a check \
that examined nothing"
  if !undeclaredSkips.isEmpty then
    problems := problems.push
      s!"constant(s) left out of the kernel re-check for a reason not on the declared list \
{declaredSkipReasons}: {undeclaredSkips}"
  if !unsafeFamilies.isEmpty then
    problems := problems.push
      s!"inductive family(ies) declared unsafe: {unsafeFamilies}. This library has none, and an \
unsafe family would put its constructors and recursors outside what the re-check covers, so it is \
refused rather than skipped quietly."
  if accounted != scanned then
    problems := problems.push
      s!"the kernel re-check accounted for {accounted} of the {scanned} constant(s) scanned. Every \
constant must land in exactly one bucket — re-added, rejected, skipped for a declared reason, or \
covered as part of an inductive family — so a mismatch means the classification silently lost \
one."
  if !missingCtors.isEmpty then
    problems := problems.push
      s!"inductive constructor(s) named by their type but absent from the environment, so the \
family was re-added with fewer constructors than it declares: {missingCtors}"

  if problems.size > 0 then
    let report := "\n  - " ++ String.intercalate "\n  - " problems.toList
    throwError s!"AUDIT FAILED — reasons:{report}"

  IO.println "extra axioms: (none) PASS"
