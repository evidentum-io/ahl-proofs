import AhlProofs.Closure.Model

/-!
# Lemma 2 — revocation completeness relative to a checkpoint

Source: AHL invariants page Section 2, whose own sources are I-D revision 0.4 Section 5.1
(affected set, seeding rules), Section 5.2 (completeness relative to the declared checkpoint D),
Section 5.3 (the boundary), Section 5.4 (cycles), Section 3.1 item 5 (authenticated
enumeration) and Section 6.1 L3.

The page's letters are kept exactly; each is quoted in the doc comment of the theorem that
carries it.

-- AMBIGUITY: the invariants page and the working brief label the clauses differently. The page
-- reads: 2a = existence, uniqueness, termination; 2b = determinism / decidability of
-- disagreement; 2c = monotonicity in the checkpoint; 2d = the seeding rules differ. The brief's
-- paraphrase attaches (b) to the least-fixed-point property, (c) to determinism and (d) to
-- monotonicity. The brief itself says to follow the page's letters exactly, and that is what is
-- done here; the least-fixed-point content the brief attaches to (b) is part of 2a, which is
-- where the page puts it (`lfp F_t`).
-/

namespace AhlProofs.Closure

variable {V : Type}

/-! ## The affected set

`F_t(A) = seeds(t) ∪ { o | ∃ i ∈ A, (i → o) ∈ G_C, scope S covers }` and
`affected(t, C) = lfp F_t` (invariants page Section 2). `Reaches` is that least fixed point,
given as an inductive predicate: an order-free definition, which is what makes Lemma 2b a
statement about the specification rather than about one traversal strategy. -/

/-- Membership in the affected set: a record is reached from the seeds by scope-covered edges
of `G_C`. Note that the seeds are members, as they are in the page's `F_t`.

-- AMBIGUITY: `ahl-core`'s `Closure` value splits the same set into two fields, `seeds` and
-- `affected`, with the seeds excluded from `affected`. The page's `lfp F_t` includes them.
-- This development follows the page; `Reaches … r` therefore corresponds to
-- `r ∈ closure.seeds ∪ closure.affected` on the Rust side. -/
inductive Reaches (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) :
    RecordRef → Prop where
  /-- Every seed is affected (I-D Section 5.1: "The trigger's scope applies to every seed"). -/
  | seed {r : RecordRef} (h : r ∈ seeds) : Reaches E S seeds r
  /-- A consumer of an affected record, recorded by a scope-covered derivation of `G_C`, is
  affected (I-D Section 5.1: "then over the consumers of those derivations' outputs"). -/
  | step {e : Edge V} {r : RecordRef} (he : e ∈ E) (hs : S e.validTime = true)
      (hin : Reaches E S seeds e.input) (hout : e.output = r) : Reaches E S seeds r

/-- A set is closed for the closure rules when it contains every seed and is closed under
scope-covered edges — i.e. it is a post-fixed point of `F_t` in the page's notation. -/
def IsClosed (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef)
    (A : RecordRef → Prop) : Prop :=
  (∀ r ∈ seeds, A r) ∧
    (∀ e ∈ E, S e.validTime = true → A e.input → A e.output)

/-- `A` is *the* least fixed point of `F_t`: closed, and contained in every closed set. -/
def IsLeastClosed (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef)
    (A : RecordRef → Prop) : Prop :=
  IsClosed E S seeds A ∧ ∀ B, IsClosed E S seeds B → ∀ r, A r → B r

/-! ## Lemma 2a — existence, uniqueness, termination

Page: «`G_C` конечен, `F_t` монотонна по `⊆` → по Кнастеру–Тарскому lfp существует и
единственна; итерация Клини с `∅` достигает её за `≤ |RecordRef(G_C)|` шагов. Это формализует
"MUST NOT loop" §5.4: циклы в `G_C` не мешают, потому что итерируем множество, а не пути.» -/

/-- The affected set is closed (the fixed-point half of Lemma 2a). -/
theorem reaches_isClosed (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) :
    IsClosed E S seeds (Reaches E S seeds) :=
  ⟨fun _ h => .seed h, fun _ he hs hin => .step he hs hin rfl⟩

/-- The affected set is contained in every closed set (the leastness half of Lemma 2a). -/
theorem reaches_least (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef)
    {B : RecordRef → Prop} (hB : IsClosed E S seeds B) :
    ∀ r, Reaches E S seeds r → B r := by
  intro r hr
  induction hr with
  | seed h => exact hB.1 _ h
  | step he hs _ hout ih => exact hout ▸ hB.2 _ he hs ih

/-- **Lemma 2a, existence.** The affected set is the least fixed point of the Section 5.1
closure operator. Cycles in `G_C` are no obstacle — the definition iterates a set, not paths
(I-D Section 5.4, "MUST NOT loop"). -/
theorem reaches_isLeastClosed (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) :
    IsLeastClosed E S seeds (Reaches E S seeds) :=
  ⟨reaches_isClosed E S seeds, fun _ hB => reaches_least E S seeds hB⟩

/-- **Lemma 2a, uniqueness.** Two least fixed points of the same closure operator are the same
set — so "the" affected set is well defined, whatever route a verifier takes to it. -/
theorem isLeastClosed_unique {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef}
    {A B : RecordRef → Prop} (hA : IsLeastClosed E S seeds A) (hB : IsLeastClosed E S seeds B) :
    A = B := by
  funext r
  exact propext ⟨fun h => hA.2 B hB.1 r h, fun h => hB.2 A hA.1 r h⟩

/-- Any least fixed point of the closure operator is the affected set. -/
theorem eq_reaches_of_isLeastClosed {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef}
    {A : RecordRef → Prop} (hA : IsLeastClosed E S seeds A) : A = Reaches E S seeds :=
  isLeastClosed_unique hA (reaches_isLeastClosed E S seeds)

/-! ## Lemma 2a, termination: the Kleene iteration and its bound

Two list utilities first. Neither is in Lean's prelude and neither needs Mathlib.
-/

/-- Filtering by a stronger predicate keeps no more elements. -/
theorem length_filter_le_of_imp {α : Type} {p q : α → Bool} (h : ∀ x, q x = true → p x = true) :
    ∀ l : List α, (l.filter q).length ≤ (l.filter p).length
  | [] => by simp
  | x :: xs => by
    have ih := length_filter_le_of_imp h xs
    by_cases hq : q x = true
    · have hp := h x hq
      simp only [List.filter_cons, hq, hp, if_pos, List.length_cons]
      omega
    · simp only [Bool.not_eq_true] at hq
      by_cases hp : p x = true
      · simp only [List.filter_cons, hq, hp, if_pos, if_neg, List.length_cons,
          Bool.false_eq_true, not_false_eq_true]
        omega
      · simp only [Bool.not_eq_true] at hp
        simp only [List.filter_cons, hq, hp, if_neg, Bool.false_eq_true, not_false_eq_true]
        omega

/-- Filtering by a strictly stronger predicate — one element of the list satisfies `p` but not
`q` — keeps strictly fewer elements. This is the counting step behind the iteration bound. -/
theorem length_filter_lt_of_witness {α : Type} {p q : α → Bool}
    (h : ∀ x, q x = true → p x = true) {a : α} :
    ∀ {l : List α}, a ∈ l → p a = true → q a = false →
      (l.filter q).length < (l.filter p).length
  | x :: xs, ha, hpa, hqa => by
    have hle := length_filter_le_of_imp h xs
    rcases List.mem_cons.mp ha with rfl | hmem
    · simp only [List.filter_cons, hpa, hqa, if_pos, if_neg, List.length_cons,
        Bool.false_eq_true, not_false_eq_true]
      omega
    · have ih := length_filter_lt_of_witness h hmem hpa hqa
      by_cases hq : q x = true
      · have hp := h x hq
        simp only [List.filter_cons, hq, hp, if_pos, List.length_cons]
        omega
      · simp only [Bool.not_eq_true] at hq
        by_cases hp : p x = true
        · simp only [List.filter_cons, hq, hp, if_pos, if_neg, List.length_cons,
            Bool.false_eq_true, not_false_eq_true]
          omega
        · simp only [Bool.not_eq_true] at hp
          simp only [List.filter_cons, hq, hp, if_neg, Bool.false_eq_true, not_false_eq_true]
          omega

/-- Duplicate removal, so that the iteration bound counts *distinct* record references — the
page's `|RecordRef(G_C)|`. Written out rather than taken from `List.eraseDups`, which would
require a `LawfulBEq` instance this development has no other use for. -/
def nub : List RecordRef → List RecordRef
  | [] => []
  | x :: xs => let r := nub xs; if x ∈ r then r else x :: r

@[simp] theorem mem_nub {x : RecordRef} : ∀ {l : List RecordRef}, x ∈ nub l ↔ x ∈ l
  | [] => by simp [nub]
  | y :: ys => by
    simp only [nub]
    by_cases h : y ∈ nub ys
    · simp only [h, if_pos, List.mem_cons, mem_nub]
      constructor
      · exact fun hx => Or.inr hx
      · rintro (rfl | hx)
        · exact mem_nub.mp h
        · exact hx
    · simp only [h, if_neg, not_false_eq_true, List.mem_cons, mem_nub]

/-- `RecordRef(G_C)` together with the seeds: every record reference the closure can ever
mention, without duplicates. Its length is the page's bound on the number of Kleene steps. -/
def carrier (E : List (Edge V)) (seeds : List RecordRef) : List RecordRef :=
  nub (seeds ++ E.map Edge.input ++ E.map Edge.output)

/-- One Kleene step: `F_t` applied to a list of records (`ahl-core` `affected_set` performs the
same step, breadth-first, with a `seen` set bounding the walk). -/
def stepList (E : List (Edge V)) (S : Scope V) (acc : List RecordRef) : List RecordRef :=
  acc ++ (E.filter fun e => S e.validTime && decide (e.input ∈ acc)).map Edge.output

/-- The Kleene iteration from the seeds: `level 0 = seeds`, `level (k+1) = F_t (level k)`. -/
def level (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) : Nat → List RecordRef
  | 0 => seeds
  | k + 1 => stepList E S (level E S seeds k)

theorem mem_stepList {E : List (Edge V)} {S : Scope V} {acc : List RecordRef} {x : RecordRef} :
    x ∈ stepList E S acc ↔
      x ∈ acc ∨ ∃ e ∈ E, S e.validTime = true ∧ e.input ∈ acc ∧ e.output = x := by
  simp only [stepList, List.mem_append, List.mem_map, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro (h | ⟨e, ⟨he, hs, hin⟩, hout⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, he, hs, hin, hout⟩
  · rintro (h | ⟨e, he, hs, hin, hout⟩)
    · exact Or.inl h
    · exact Or.inr ⟨e, ⟨he, hs, hin⟩, hout⟩

theorem mem_level_succ_of_mem {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef}
    {k : Nat} {x : RecordRef} (h : x ∈ level E S seeds k) : x ∈ level E S seeds (k + 1) :=
  mem_stepList.mpr (Or.inl h)

theorem mem_level_of_le {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef}
    {j k : Nat} (hjk : j ≤ k) {x : RecordRef} (h : x ∈ level E S seeds j) :
    x ∈ level E S seeds k := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction i with
  | zero => exact h
  | succ i ih => exact mem_level_succ_of_mem ih

theorem stepList_mono {E : List (Edge V)} {S : Scope V} {a b : List RecordRef}
    (hab : ∀ y, y ∈ a → y ∈ b) {x : RecordRef} (h : x ∈ stepList E S a) : x ∈ stepList E S b := by
  rcases mem_stepList.mp h with h | ⟨e, he, hs, hin, hout⟩
  · exact mem_stepList.mpr (Or.inl (hab _ h))
  · exact mem_stepList.mpr (Or.inr ⟨e, he, hs, hab _ hin, hout⟩)

theorem mem_carrier_of_mem_level {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef} :
    ∀ {k : Nat} {x : RecordRef}, x ∈ level E S seeds k → x ∈ carrier E seeds
  | 0, _, h => by
    simp only [carrier, mem_nub, List.mem_append]
    exact Or.inl (Or.inl h)
  | k + 1, x, h => by
    rcases mem_stepList.mp h with h | ⟨e, he, _, _, hout⟩
    · exact mem_carrier_of_mem_level h
    · simp only [carrier, mem_nub, List.mem_append, List.mem_map]
      exact Or.inr ⟨e, he, hout⟩

/-- The Kleene iterate is sound: everything it reaches is affected. -/
theorem reaches_of_mem_level {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef} :
    ∀ {k : Nat} {x : RecordRef}, x ∈ level E S seeds k → Reaches E S seeds x
  | 0, _, h => .seed h
  | _ + 1, _, h => by
    rcases mem_stepList.mp h with h | ⟨e, he, hs, hin, hout⟩
    · exact reaches_of_mem_level h
    · exact .step he hs (reaches_of_mem_level hin) hout

/-- The Kleene iteration is complete: every affected record appears at some stage. -/
theorem exists_mem_level_of_reaches {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef}
    {x : RecordRef} (h : Reaches E S seeds x) : ∃ k, x ∈ level E S seeds k := by
  induction h with
  | seed h => exact ⟨0, h⟩
  | step he hs _ hout ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, mem_stepList.mpr (Or.inr ⟨_, he, hs, hk, hout⟩)⟩

/-- The iteration has stabilised at stage `k`: stage `k + 1` reaches nothing new. -/
def Stable (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) (k : Nat) : Prop :=
  ∀ x, x ∈ level E S seeds (k + 1) → x ∈ level E S seeds k

theorem stable_forever {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef} {k : Nat}
    (hk : Stable E S seeds k) :
    ∀ (i : Nat) (x : RecordRef), x ∈ level E S seeds (k + i) → x ∈ level E S seeds k := by
  intro i
  induction i with
  | zero => exact fun _ h => h
  | succ i ih =>
    intro x h
    have : x ∈ level E S seeds (k + 1) := by
      have hstep : x ∈ stepList E S (level E S seeds (k + i)) := h
      exact stepList_mono ih hstep
    exact hk x this

/-- How many carrier records the iteration has not reached by stage `k`. It bounds the number
of steps that can still do anything. -/
def deficit (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) (k : Nat) : Nat :=
  ((carrier E seeds).filter fun x => !decide (x ∈ level E S seeds k)).length

theorem deficit_le_carrier (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) (k : Nat) :
    deficit E S seeds k ≤ (carrier E seeds).length :=
  List.length_filter_le _ _

/-- A step that is not yet stable consumes at least one carrier record. -/
theorem deficit_lt_of_not_stable {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef}
    {k : Nat} (h : ¬ Stable E S seeds k) :
    deficit E S seeds (k + 1) < deficit E S seeds k := by
  have hex : ∃ x, x ∈ level E S seeds (k + 1) ∧ x ∉ level E S seeds k := by
    by_cases hc : ∃ x, x ∈ level E S seeds (k + 1) ∧ x ∉ level E S seeds k
    · exact hc
    · exact absurd (fun x hx => Classical.byContradiction fun hn => hc ⟨x, hx, hn⟩) h
  obtain ⟨x, hx1, hx2⟩ := hex
  refine length_filter_lt_of_witness ?_ (mem_carrier_of_mem_level hx1) ?_ ?_
  · intro y hy
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hy ⊢
    exact fun hmem => hy (mem_level_succ_of_mem hmem)
  · simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    exact hx2
  · simp only [Bool.not_eq_false', decide_eq_true_eq]
    exact hx1

/-- Every unstable stage costs one carrier record, so instability cannot outlast the carrier. -/
theorem descent {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef} :
    ∀ {i : Nat}, (∀ j, j < i → ¬ Stable E S seeds j) →
      deficit E S seeds i + i ≤ deficit E S seeds 0
  | 0, _ => by omega
  | i + 1, h => by
    have ih := descent (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hstep := deficit_lt_of_not_stable (h i (Nat.lt_succ_self i))
    omega

/-- **Lemma 2a, termination.** The Kleene iteration from the seeds stabilises within
`|RecordRef(G_C)| ∪ seeds` steps — the page's «за `≤ |RecordRef(G_C)|` шагов». -/
theorem exists_stable (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) :
    ∃ j, j ≤ (carrier E seeds).length ∧ Stable E S seeds j :=
  Classical.byContradiction fun hcon => by
    have h : ∀ j, j < (carrier E seeds).length + 1 → ¬ Stable E S seeds j := by
      intro j hj hs
      exact hcon ⟨j, by omega, hs⟩
    have hd := descent h
    have h0 := deficit_le_carrier E S seeds 0
    omega

/-- The stage the bound names is stable: iterating further reaches nothing new. -/
theorem stable_carrier_length (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) :
    Stable E S seeds (carrier E seeds).length := by
  obtain ⟨j, hjN, hj⟩ := exists_stable E S seeds
  intro x hx
  obtain ⟨i, hi⟩ := Nat.exists_eq_add_of_le hjN
  have hxj : x ∈ level E S seeds j := by
    refine stable_forever hj (i + 1) x ?_
    have : j + (i + 1) = (carrier E seeds).length + 1 := by omega
    exact this ▸ hx
  exact mem_level_of_le hjN hxj

/-- **The affected set, computed.** `affected_set` is the Kleene iteration run for the number
of steps Lemma 2a bounds it by; it is a total, decidable function of the edge list, the scope
and the seeds (`ahl-core` `closure::affected_set`, which performs the same iteration
breadth-first). -/
def affected_set (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef) : List RecordRef :=
  level E S seeds (carrier E seeds).length

/-- **Lemma 2a, existence and termination together.** The computed affected set has exactly the
members of the least fixed point: the iteration is sound, complete, and finished at the bound.
Cycles cannot make it loop — the iteration is over a set, not over paths (I-D Section 5.4). -/
theorem mem_affected_set_iff_reaches {E : List (Edge V)} {S : Scope V} {seeds : List RecordRef}
    {x : RecordRef} : x ∈ affected_set E S seeds ↔ Reaches E S seeds x := by
  constructor
  · exact reaches_of_mem_level
  · intro h
    obtain ⟨j, hjN, hj⟩ := exists_stable E S seeds
    obtain ⟨k, hk⟩ := exists_mem_level_of_reaches h
    rcases Nat.le_total k j with hkj | hjk
    · exact mem_level_of_le (Nat.le_trans hkj hjN) hk
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hjk
      exact mem_level_of_le hjN (stable_forever hj i x hk)

/-! ## The affected set of a trigger at a checkpoint

The log-level definitions the page's `affected(t, C)` names: `G_C` is `edges log treeSize`,
`seeds(t)` is `trigger_seeds log t`, and the scope is the trigger's own. -/

/-- `affected(t, C)` as a proposition: the record is affected by the trigger at entry index `t`,
evaluated at the checkpoint of size `treeSize` (I-D Section 5.1). -/
def Affected (log : Log V) (treeSize t : Nat) (r : RecordRef) : Prop :=
  Reaches (edges log treeSize) (trigger_scope log t) (trigger_seeds log t) r

/-- `affected(t, C)` as a computed list (`ahl-core` `affected_set`). -/
def affected_at (log : Log V) (treeSize t : Nat) : List RecordRef :=
  affected_set (edges log treeSize) (trigger_scope log t) (trigger_seeds log t)

theorem mem_affected_at_iff {log : Log V} {treeSize t : Nat} {r : RecordRef} :
    r ∈ affected_at log treeSize t ↔ Affected log treeSize t r :=
  mem_affected_set_iff_reaches

/-! ## Lemma 2b — determinism, and decidability of disagreement

Page: «Два верификатора с **одним и тем же** `S_C` получают одно `affected(t, C)`. Следствие:
сравнение с anchored disposition tree (§2.4.4) — решимая проверка равенства множеств.» -/

/-- Membership in the affected set is decidable — the Kleene iteration of Lemma 2a decides it. -/
instance instDecidableReaches (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef)
    (r : RecordRef) : Decidable (Reaches E S seeds r) :=
  decidable_of_iff _ mem_affected_set_iff_reaches

instance instDecidableAffected (log : Log V) (treeSize t : Nat) (r : RecordRef) :
    Decidable (Affected log treeSize t r) :=
  instDecidableReaches _ _ _ _

theorem edges_of_prefix_eq {log₁ log₂ : Log V} {n : Nat} (h : log₁.take n = log₂.take n) :
    edges log₁ n = edges log₂ n := by
  simp only [edges, h]

theorem take_eq_of_prefix_eq {log₁ log₂ : Log V} {n t : Nat} (hn : t < n)
    (h : log₁.take n = log₂.take n) : log₁.take t = log₂.take t := by
  have hmin : min t n = t := Nat.min_eq_left (Nat.le_of_lt hn)
  calc log₁.take t = (log₁.take n).take t := by rw [List.take_take, hmin]
    _ = (log₂.take n).take t := by rw [h]
    _ = log₂.take t := by rw [List.take_take, hmin]

theorem getElem?_of_prefix_eq {log₁ log₂ : Log V} {n t : Nat} (hn : t < n)
    (h : log₁.take n = log₂.take n) : log₁[t]? = log₂[t]? := by
  rw [← List.getElem?_take_of_lt (l := log₁) hn, ← List.getElem?_take_of_lt (l := log₂) hn, h]

theorem trigger_seeds_of_prefix_eq {log₁ log₂ : Log V} {n t : Nat} (hn : t < n)
    (h : log₁.take n = log₂.take n) : trigger_seeds log₁ t = trigger_seeds log₂ t := by
  simp only [trigger_seeds, getElem?_of_prefix_eq hn h, take_eq_of_prefix_eq hn h]

theorem trigger_scope_of_prefix_eq {log₁ log₂ : Log V} {n t : Nat} (hn : t < n)
    (h : log₁.take n = log₂.take n) : trigger_scope log₁ t = trigger_scope log₂ t := by
  simp only [trigger_scope, getElem?_of_prefix_eq hn h]

/-- **Lemma 2b.** Two verifiers holding the same corpus prefix `S_C` — the same entries below
`tree_size(C)` — compute the same affected set, whatever their traversal order. Order-freeness
is built into the statement: `Affected` is defined by the order-free `Reaches`, and
`isLeastClosed_unique` says any least fixed point whatsoever coincides with it. -/
theorem affected_of_prefix_eq {log₁ log₂ : Log V} {n t : Nat} (hn : t < n)
    (h : log₁.take n = log₂.take n) : Affected log₁ n t = Affected log₂ n t := by
  funext r
  simp only [Affected, edges_of_prefix_eq h, trigger_seeds_of_prefix_eq hn h,
    trigger_scope_of_prefix_eq hn h]

/-- The same statement for the computed set: two verifiers get the same list, not merely the
same membership. -/
theorem affected_at_of_prefix_eq {log₁ log₂ : Log V} {n t : Nat} (hn : t < n)
    (h : log₁.take n = log₂.take n) : affected_at log₁ n t = affected_at log₂ n t := by
  simp only [affected_at, edges_of_prefix_eq h, trigger_seeds_of_prefix_eq hn h,
    trigger_scope_of_prefix_eq hn h]

/-- **Lemma 2b, corollary.** Comparing the recomputed affected set against an anchored
disposition list (I-D Section 2.4.4) is a finite, decidable equality check — the page's
«решимая проверка равенства множеств». -/
theorem agreement_iff (E : List (Edge V)) (S : Scope V) (seeds : List RecordRef)
    (claimed : List RecordRef) :
    (∀ r, Reaches E S seeds r ↔ r ∈ claimed) ↔
      ((∀ r ∈ affected_set E S seeds, r ∈ claimed) ∧
        ∀ r ∈ claimed, r ∈ affected_set E S seeds) := by
  constructor
  · intro h
    exact ⟨fun r hr => (h r).mp (mem_affected_set_iff_reaches.mp hr),
      fun r hr => mem_affected_set_iff_reaches.mpr ((h r).mpr hr)⟩
  · intro ⟨h₁, h₂⟩ r
    exact ⟨fun hr => h₁ r (mem_affected_set_iff_reaches.mpr hr),
      fun hr => mem_affected_set_iff_reaches.mp (h₂ r hr)⟩

instance instDecidableAgreement (E : List (Edge V)) (S : Scope V) (seeds claimed : List RecordRef) :
    Decidable (∀ r, Reaches E S seeds r ↔ r ∈ claimed) :=
  decidable_of_iff _ (agreement_iff E S seeds claimed).symm

/-! ## Lemma 2c — monotonicity in the checkpoint

Page: «Если `C' ⊒ C` … то `affected(t, C) ⊆ affected(t, C')`. Новые деривации только добавляют
рёбра; `F` растёт поточечно; lfp монотонна по оператору.» -/

/-- The closure is monotone in the edge set: more edges never remove an affected record. -/
theorem reaches_mono_edges {E E' : List (Edge V)} {S : Scope V} {seeds : List RecordRef}
    (hE : ∀ e ∈ E, e ∈ E') {r : RecordRef} (h : Reaches E S seeds r) : Reaches E' S seeds r := by
  induction h with
  | seed h => exact .seed h
  | step he hs _ hout ih => exact .step (hE _ he) hs ih hout

/-- A later checkpoint only adds edges (I-D Section 5.2, "enlargement"). -/
theorem edges_mono {log : Log V} {n n' : Nat} (hn : n ≤ n') :
    ∀ e ∈ edges log n, e ∈ edges log n' := by
  intro e he
  obtain ⟨entry, hentry, hedge⟩ := List.mem_flatMap.mp he
  refine List.mem_flatMap.mpr ⟨entry, ?_, hedge⟩
  have hmin : min n n' = n := Nat.min_eq_left hn
  have : log.take n = (log.take n').take n := by rw [List.take_take, hmin]
  exact List.take_subset _ _ (this ▸ hentry)

/-- **Lemma 2c.** For `C' ⊒ C` — a checkpoint over a longer prefix of the same log — the
affected set at `C` is contained in the affected set at `C'`. The trigger, and hence the seeds
and the scope, are unchanged: they are read from the trigger's own entry. -/
theorem affected_mono {log : Log V} {n n' t : Nat} (hn : n ≤ n') {r : RecordRef}
    (h : Affected log n t r) : Affected log n' t r :=
  reaches_mono_edges (edges_mono hn) h

/-! ## Lemma 2d — the seeding rules genuinely differ

Page: «Существуют `S_C`, где `affected(retraction X) ≠ affected(correction X→Xnew)` при равных
scope. Лемма-контрпример: корпус `vectors/closure/retraction-after-correction.json` уже
является свидетелем. Нужна, чтобы §5.1 нельзя было "упростить" в одну строку.»

The witness below is the shape of that corpus scenario, reduced to its essentials: a record
corrected earlier in the corpus, a consumer of the superseded replacement, and then the two
triggers on the same record with the same scope. The retraction seeds `{X}` and does not reach
the consumer; the later correction seeds `{X, Xold}` and does.

-- AMBIGUITY: the page says "there exist `S_C`" without fixing one. Rather than transcribing
-- the 57-entry toy corpus, the witness is the smallest log exhibiting the distinction; the
-- corpus vector `retraction-after-correction.json` (and its contrast `supersession-chain.json`)
-- is the test-evidence counterpart of the same fact, not its proof. -/

/-- The original record `X` of the scenario. -/
def demoX : RecordRef := { dataset := "customers", record := "A" }
/-- The superseded replacement `Xold`, produced by the earlier correction. -/
def demoXold : RecordRef := { dataset := "customers", record := "A2" }
/-- The later correction's own replacement `Xnew`, never a seed. -/
def demoXnew : RecordRef := { dataset := "customers", record := "A3" }
/-- A record derived from `Xold`. -/
def demoY : RecordRef := { dataset := "scores", record := "S1" }

/-- A retroactive scope: it covers every derivation (I-D Section 2.4.3). -/
def demoScope : Scope Unit := fun _ => true

/-- The witness corpus: introduction, an earlier correction X to Xold, a derivation consuming
Xold, then the two triggers on X with the same scope. -/
def demoLog : Log Unit :=
  [ { statement := .ingestion demoX, void := false },
    { statement := .correction demoX demoXold demoScope, void := false },
    { statement := .derivation [demoXold] [demoY] (), void := false },
    { statement := .retraction demoX demoScope, void := false },
    { statement := .correction demoX demoXnew demoScope, void := false } ]

example : trigger_seeds demoLog 3 = [demoX] := by decide
example : trigger_seeds demoLog 4 = [demoX, demoXold] := by decide
example : trigger_scope demoLog 3 = trigger_scope demoLog 4 := rfl

/-- **Lemma 2d.** With one and the same scope and one and the same corpus prefix, a retraction
on `X` and a correction of `X` do not have the same affected set: the correction's closure
reaches the consumer of a superseded replacement, and the retraction's does not. Section 5.1
cannot be collapsed into a single seeding rule. -/
theorem seeding_rules_differ :
    ∃ (log : Log Unit) (n t_retraction t_correction : Nat) (r : RecordRef),
      trigger_scope log t_retraction = trigger_scope log t_correction ∧
      Affected log n t_correction r ∧ ¬ Affected log n t_retraction r :=
  ⟨demoLog, 5, 3, 4, demoY, rfl, by decide, by decide⟩

/-- The same fact stated as the page states it: the two affected sets are different sets. -/
theorem affected_retraction_ne_correction :
    Affected demoLog 5 3 ≠ Affected demoLog 5 4 := by
  intro h
  have hy : Affected demoLog 5 4 demoY := by decide
  rw [← h] at hy
  exact (by decide : ¬ Affected demoLog 5 3 demoY) hy

/-! ## Void entries contribute nothing (I-D Section 7.5.1 erratum 4d)

«A non-verifying envelope is VOID … it is never effective and never traversed.» In this model
that is a definition (`edgesOf`, `trigger_seeds`); the consequences a verifier relies on are
stated here as theorems. -/

/-- A void entry records no closure edge. -/
@[simp] theorem edgesOf_void {e : Entry V} (h : e.void = true) : edgesOf e = [] := by
  simp only [edgesOf, h, if_pos]

/-- A void trigger seeds nothing: it is never effective (I-D Section 7.5.1 4d, 4e). -/
@[simp] theorem trigger_seeds_void {log : Log V} {t : Nat} {e : Entry V}
    (hget : log[t]? = some e) (h : e.void = true) : trigger_seeds log t = [] := by
  simp only [trigger_seeds, hget, h, if_pos]

/-- A void trigger has an empty affected set: nothing is reached from no seeds, since the
closure has nowhere to start. -/
theorem not_affected_of_void_trigger {log : Log V} {treeSize t : Nat} {e : Entry V}
    (hget : log[t]? = some e) (h : e.void = true) (r : RecordRef) :
    ¬ Affected log treeSize t r := by
  intro hr
  have : ∀ x, Reaches (edges log treeSize) (trigger_scope log t) (trigger_seeds log t) x → False :=
    reaches_least _ _ _ ⟨by simp [trigger_seeds_void hget h], fun _ _ _ hin => hin⟩
  exact this r hr

/-- A void entry at the head of a log removes exactly its own edges: the closure walks only
verifying statements. -/
theorem edges_cons_void {e : Entry V} (h : e.void = true) (rest : Log V) (n : Nat) :
    edges (e :: rest) (n + 1) = edges rest n := by
  simp only [edges, List.take_succ_cons, List.flatMap_cons, edgesOf_void h, List.nil_append]

end AhlProofs.Closure
