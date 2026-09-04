/-!
# The closure model (AHL invariants page, Sections 0 and 2)

The abstract corpus over which Lemma 2 — revocation completeness relative to a checkpoint — is
stated. Sources: AHL I-D revision 0.4, Section 2.4 (statement types; `retraction` and
`correction`), Section 5.1 (the affected set: seeding rules and the edge rule), Section 5.3
(completeness is relative to the declared corpus at the checkpoint), Section 5.4 (cycles),
Section 7.2 (`propagation-complete`), Section 7.5.1 erratum 4d (a void entry is never
traversed).

Nothing cryptographic enters Lemma 2. There is no hash, no signature and no assumption
parameter in this file: the whole lemma is about a finite graph computation over the prefix a
checkpoint commits. Time never appears either — the invariants page fixes «порядок = позиция»,
so an entry index is a `List` position and a scope is an abstract predicate on an abstract
valid-time type.

Names follow `ahl-core/src/closure.rs` (`RecordRef`, `Edge`, `edges`, `trigger_seeds`,
`affected_set`) so the two can be read side by side. That is a convenience for the reader and
not a proof of anything about the implementation (see `AhlProofs/Closure/Boundary.lean`).
-/

namespace AhlProofs.Closure

/-- A `(dataset, record)` pair — the only identity closure traversal uses
(I-D Section 2.4.2: "Closure traversal (Section 5.1) uses the `(dataset, record)` pair only");
`ahl-core` `pub type RecordRef = (String, String)`.

-- AMBIGUITY: the invariants page writes `RecordRef = (ds, r)` without saying what a dataset id
-- or a record commitment is. Lemma 2 never inspects either component — it only compares record
-- references — so they are modelled as `String`, matching the Rust type, and every proof below
-- goes through for any type with decidable equality. -/
structure RecordRef where
  /-- Dataset id (I-D Section 2.6). -/
  dataset : String
  /-- Record commitment (I-D Section 2.6). -/
  record : String
deriving DecidableEq, Repr, Inhabited

/-- A trigger's scope, as a criterion on a derivation's asserted valid time
(I-D Section 2.4.3: with `retroactive: true` every consuming derivation is affected; with
`retroactive: false` a derivation is affected iff its `valid_time` intersects
`[effective_from, ∞)`).

-- AMBIGUITY: the invariants page writes the closure operator as
-- `F_t(A) = seeds(t) ∪ { o | ∃ i ∈ A, (i → o) ∈ G_C, scope S covers o }`, i.e. it phrases the
-- scope filter as applying to the OUTPUT record. The I-D (Section 2.4.3) and `ahl-core`
-- (`closure.rs`: `if scope.covers(edge.valid_time)`) both filter the DERIVATION by its
-- `valid_time`; a record reference carries no time of its own, so the page's phrasing is
-- shorthand. This model filters edges, following the I-D and the implementation. -/
abbrev Scope (V : Type) := V → Bool

/-- A statement, reduced to the members the closure rules read (I-D Section 2.4).

`V` is the type of asserted valid times, left abstract: no lemma interprets it. -/
inductive Statement (V : Type) where
  /-- `ingestion` — introduces a source record (I-D Section 2.4.1). Contributes no closure
  edges: an introduction consumes nothing. -/
  | ingestion (output : RecordRef)
  /-- `derivation` — outputs produced from inputs, carrying the asserted valid time the
  trigger's scope is tested against (I-D Section 2.4.2). -/
  | derivation (inputs outputs : List RecordRef) (validTime : V)
  /-- `retraction` on `(ds, X)` (I-D Section 2.4.3). -/
  | retraction (target : RecordRef) (scope : Scope V)
  /-- `correction` X to Xnew (I-D Section 2.4.3). -/
  | correction (target replacement : RecordRef) (scope : Scope V)
  /-- Any statement kind the closure rules do not read — `propagation`, `manifest`, `key`,
  `disposition` (I-D Sections 2.4.4 to 2.4.6). -/
  | other

/-- A log entry: a statement plus the erratum-4d void flag.

I-D Section 7.5.1 erratum 4d: an entry an enumeration reveals whose envelope does not verify
"is VOID … it is never effective and never traversed". Voidness is decided by envelope
verification, which is outside this model, so it is carried as a flag. -/
structure Entry (V : Type) where
  /-- The statement the entry anchors. -/
  statement : Statement V
  /-- `true` when the entry's envelope does not verify (I-D Section 7.5.1 4d). A void entry
  contributes no seeds and no edges. -/
  void : Bool

/-- A log: entries in entry-index order. The index of an entry is its position, per the
invariants page («порядок = позиция», constitution article 9). -/
abbrev Log (V : Type) := List (Entry V)

/-- One consumption edge: an input record was read to produce an output record
(`ahl-core` `struct Edge`).

-- AMBIGUITY: `ahl-core`'s `Edge` also carries `entry_index`. It is dropped here because no
-- clause of Lemma 2 reads it — the prefix restriction is already expressed by taking the first
-- `tree_size` entries — and carrying it would make the edge list depend on positions that
-- nothing consumes. -/
structure Edge (V : Type) where
  /-- The recording derivation's asserted valid time, used for scope filtering. -/
  validTime : V
  /-- The consumed input record. -/
  input : RecordRef
  /-- The produced output record. -/
  output : RecordRef

/-- The edges a single entry contributes (I-D Section 5.1: the closure runs "over derivations
… whose inputs match `(ds, X)`, then over the consumers of those derivations' outputs").

A void entry contributes none (I-D Section 7.5.1 4d); so does every statement kind other than
`derivation`. -/
def edgesOf {V : Type} (e : Entry V) : List (Edge V) :=
  if e.void then [] else
    match e.statement with
    | .derivation inputs outputs validTime =>
        inputs.flatMap fun i => outputs.map fun o => { validTime := validTime, input := i, output := o }
    | _ => []

/-- `G_C`: every edge recorded by an entry with index below `tree_size` — the graph the closure
walks at checkpoint `C` (I-D Section 5.1, "derivations with entry index less than
`tree_size(C)`"; `ahl-core` `closure::edges`). -/
def edges {V : Type} (log : Log V) (treeSize : Nat) : List (Edge V) :=
  (log.take treeSize).flatMap edgesOf

/-- The replacements of every earlier non-void correction of the same original record, other
than the trigger's own replacement — the "previously superseded replacements" of I-D
Section 5.1, third seeding rule (`ahl-core` `trigger_seeds`, the loop over earlier entries). -/
def supersededReplacements {V : Type} (earlier : Log V) (target ownReplacement : RecordRef) :
    List RecordRef :=
  earlier.filterMap fun e =>
    if e.void then none else
      match e.statement with
      | .correction t r _ => if t = target ∧ r ≠ ownReplacement then some r else none
      | _ => none

/-- `seeds(t)`: the records a trigger at entry index `t` starts the closure from
(I-D Section 5.1 seeding rules; `ahl-core` `trigger_seeds`).

* a **retraction** on `(ds, X)` seeds exactly `{(ds, X)}` — "a retraction never seeds
  superseded replacements";
* a **correction** X to Xnew seeds X together with every previously superseded replacement of
  the same X, and never its own replacement Xnew;
* a correction targeting Xold independently starts at Xold, which is the same rule with an
  empty supersession history.

-- AMBIGUITY: `ahl-core`'s `trigger_seeds` raises an error when the entry at `t` is absent or
-- is not a trigger; a total Lean function cannot. An absent, void, or non-trigger entry yields
-- the empty seed set here, which makes the affected set empty as well. That totality is relied
-- on nowhere: every clause of Lemma 2 carries the precondition `t < tree_size` — the checkpoint
-- must commit the trigger (I-D Section 5.1, "evaluated at a checkpoint C that commits the
-- trigger") — as a conjunct of `AhlProofs.Closure.Affected`, and the closure of a non-trigger
-- is not a statement of this document. -/
def trigger_seeds {V : Type} (log : Log V) (t : Nat) : List RecordRef :=
  match log[t]? with
  | none => []
  | some e =>
      if e.void then [] else
        match e.statement with
        | .retraction target _ => [target]
        | .correction target replacement _ =>
            target :: supersededReplacements (log.take t) target replacement
        | _ => []

/-- The trigger's scope, read off the entry at index `t`. A non-trigger, void or absent entry
covers nothing, matching the empty seed set of `trigger_seeds`. -/
def trigger_scope {V : Type} (log : Log V) (t : Nat) : Scope V :=
  match log[t]? with
  | none => fun _ => false
  | some e =>
      if e.void then fun _ => false else
        match e.statement with
        | .retraction _ scope => scope
        | .correction _ _ scope => scope
        | _ => fun _ => false

end AhlProofs.Closure
