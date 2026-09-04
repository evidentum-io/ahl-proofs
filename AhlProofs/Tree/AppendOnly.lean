import AhlProofs.Tree.Model
import AhlProofs.Closure.RevocationCompleteness

/-!
# Lemma 3 — append-only consistency

Source: AHL invariants page Section 3, whose own sources are I-D revision 0.4 Section 3.1
(contract items 3 and 5), Section 3.2, Section 8.3 first paragraph, and RFC 9162 Section 2.1.4.

The page's letters are: **3a** consistency-proof soundness, **3b** inclusion soundness, **3c**
enumeration (range) soundness, **3d** the composition of Lemmas 2 and 3. Each is quoted in the
doc comment of the theorem carrying it.

-- AMBIGUITY: the working brief's paraphrase swaps 3a and 3b ("typically 3a inclusion
-- soundness … 3b consistency soundness"). The page has 3a = consistency and 3b = inclusion, and
-- the brief itself says to follow the page's letters; the page's order is used here.

Everything is stated in the form Lemma 1 uses: the conclusion is the intended property **or an
exhibited collision of `H`**. Collision resistance (I-D Section 8.1) is never a hypothesis, and
nothing is assumed about `M.H`.
-/

namespace AhlProofs.Tree

open AhlProofs AhlProofs.Closure

variable {Key : Type}

/-! ## Collisions from equal hashes

The two ways a tree hash can agree without the underlying data agreeing. Each returns the
witness pair, exactly as Lemma 1b does. -/

/-- Equal leaf hashes: equal entries, or a collision. -/
theorem leaf_eq_or_collision (M : HashModel Key) {a b : Bytes}
    (h : leafHash M a = leafHash M b) : a = b ∨ ∃ x y, Collision M.H x y := by
  by_cases hab : a = b
  · exact Or.inl hab
  · exact Or.inr ⟨_, _, fun hpre => hab (by simpa using hpre), h⟩

/-- Equal node hashes: equal children, or a collision. The children are recovered by the same
fixed-width argument Lemma 1a uses — both digests are exactly 32 octets. -/
theorem node_eq_or_collision (M : HashModel Key) {l r l' r' : Digest}
    (h : nodeHash M l r = nodeHash M l' r') :
    (l = l' ∧ r = r') ∨ ∃ x y, Collision M.H x y := by
  by_cases hpre : (0x00000001 % 256 : UInt8) :: (l.octets ++ r.octets) =
      (0x00000001 % 256 : UInt8) :: (l'.octets ++ r'.octets)
  · refine Or.inl ?_
    have happ : l.octets ++ r.octets = l'.octets ++ r'.octets := by simpa using hpre
    obtain ⟨hl, hr⟩ := List.append_inj happ (by rw [l.length_eq, l'.length_eq])
    exact ⟨Digest.eq_of_octets_eq hl, Digest.eq_of_octets_eq hr⟩
  · exact Or.inr ⟨_, _, hpre, h⟩

/-! ## The tree hash determines the leaves, up to a collision

The workhorse of all three clauses: two leaf lists of the same length with one tree hash are
the same list, or a collision has been exhibited. -/

theorem mthh_inj_aux (M : HashModel Key) :
    ∀ (N : Nat) (hs hs' : List Digest), hs.length ≤ N → hs.length = hs'.length →
      MTHh M hs = MTHh M hs' → hs = hs' ∨ ∃ x y, Collision M.H x y := by
  intro N
  induction N with
  | zero =>
    intro hs hs' hle hlen _
    have h1 : hs = [] := List.length_eq_zero_iff.mp (by omega)
    have h2 : hs' = [] := List.length_eq_zero_iff.mp (by omega)
    exact Or.inl (by rw [h1, h2])
  | succ N ih =>
    intro hs hs' hle hlen heq
    by_cases h0 : hs.length = 0
    · have e1 : hs = [] := List.length_eq_zero_iff.mp h0
      have e2 : hs' = [] := List.length_eq_zero_iff.mp (by omega)
      exact Or.inl (by rw [e1, e2])
    by_cases h1 : hs.length = 1
    · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h1
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp (by omega : hs'.length = 1)
      simp only [MTHh_singleton] at heq
      exact Or.inl (by rw [heq])
    · have h2 : 2 ≤ hs.length := by omega
      have h2' : 2 ≤ hs'.length := by omega
      rw [MTHh_eq_node M h2, MTHh_eq_node M h2'] at heq
      rcases node_eq_or_collision M heq with ⟨hL, hR⟩ | hc
      · have hkpos : 0 < splitPoint hs.length := splitPoint_pos hs.length
        have hk : splitPoint hs.length < hs.length := splitPoint_lt h2
        rcases ih (hs.take (splitPoint hs.length)) (hs'.take (splitPoint hs'.length))
            (by simp only [List.length_take]; omega)
            (by simp only [List.length_take, hlen]) hL with hle' | hc
        · rcases ih (hs.drop (splitPoint hs.length)) (hs'.drop (splitPoint hs'.length))
              (by simp only [List.length_drop]; omega)
              (by simp only [List.length_drop, hlen]) hR with hri | hc
          · refine Or.inl ?_
            calc hs = hs.take (splitPoint hs.length) ++ hs.drop (splitPoint hs.length) :=
                  (List.take_append_drop _ _).symm
              _ = hs'.take (splitPoint hs'.length) ++ hs'.drop (splitPoint hs'.length) := by
                  rw [hle', hri]
              _ = hs' := List.take_append_drop _ _
          · exact Or.inr hc
        · exact Or.inr hc
      · exact Or.inr hc

/-- **The tree hash determines the leaf hashes.** Two leaf-hash lists of the same length with
the same tree hash are equal, or a collision of `H` has been exhibited. -/
theorem mthh_inj_or_collision (M : HashModel Key) {hs hs' : List Digest}
    (hlen : hs.length = hs'.length) (h : MTHh M hs = MTHh M hs') :
    hs = hs' ∨ ∃ x y, Collision M.H x y :=
  mthh_inj_aux M hs.length hs hs' (Nat.le_refl _) hlen h

theorem map_leafHash_inj_or_collision (M : HashModel Key) :
    ∀ {L L' : List Bytes}, L.map (leafHash M) = L'.map (leafHash M) →
      L = L' ∨ ∃ x y, Collision M.H x y
  | [], [], _ => Or.inl rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases leaf_eq_or_collision M h.1 with hab | hc
    · rcases map_leafHash_inj_or_collision M h.2 with hrest | hc
      · exact Or.inl (by rw [hab, hrest])
      · exact Or.inr hc
    · exact Or.inr hc

/-- **The tree hash determines the entries.** Two entry lists of the same length with the same
`MTH` are equal, or a collision of `H` has been exhibited. -/
theorem mth_inj_or_collision (M : HashModel Key) {L L' : List Bytes}
    (hlen : L.length = L'.length) (h : MTH M L = MTH M L') :
    L = L' ∨ ∃ x y, Collision M.H x y := by
  rcases mthh_inj_or_collision M (by simp [hlen]) h with hmap | hc
  · exact map_leafHash_inj_or_collision M hmap
  · exact Or.inr hc

/-! ## Lemma 3b — inclusion soundness

Page: «`Incl(leaf, i, n, MTH(L_n), π) = true` → `L_n[i] = leaf`, либо коллизия.» -/

theorem rootFromPath_one (M : HashModel Key) (leafH : Digest) (i : Nat) :
    rootFromPath M leafH i 1 [] = some leafH := by
  rw [rootFromPath]; simp

theorem rootFromPath_one_cons (M : HashModel Key) (leafH p : Digest) (i : Nat)
    (rest : List Digest) : rootFromPath M leafH i 1 (p :: rest) = none := by
  rw [rootFromPath]; simp

theorem rootFromPath_nil (M : HashModel Key) (leafH : Digest) {i n : Nat} (h : 2 ≤ n) :
    rootFromPath M leafH i n [] = none := by
  rw [rootFromPath]
  have h0 : ¬ (n = 0) := by omega
  have h1 : ¬ (n = 1) := by omega
  simp [h0, h1]

theorem rootFromPath_cons (M : HashModel Key) (leafH : Digest) {i n : Nat} (h : 2 ≤ n)
    (p : Digest) (rest : List Digest) :
    rootFromPath M leafH i n (p :: rest) =
      if i < splitPoint n then
        (rootFromPath M leafH i (splitPoint n) rest).map fun l => nodeHash M l p
      else
        (rootFromPath M leafH (i - splitPoint n) (n - splitPoint n) rest).map fun r =>
          nodeHash M p r := by
  rw [rootFromPath]
  have h0 : ¬ (n = 0) := by omega
  have h1 : ¬ (n = 1) := by omega
  simp [h0, h1]

theorem inclusion_sound_aux (M : HashModel Key) :
    ∀ (N : Nat) (hs : List Digest) (leafH : Digest) (i : Nat) (path : List Digest),
      hs.length ≤ N → i < hs.length →
      rootFromPath M leafH i hs.length path = some (MTHh M hs) →
      hs[i]? = some leafH ∨ ∃ x y, Collision M.H x y := by
  intro N
  induction N with
  | zero => intro hs _ i _ hle hi _; exact False.elim (by omega)
  | succ N ih =>
    intro hs leafH i path hle hi h
    by_cases h1 : hs.length = 1
    · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h1
      cases path with
      | nil =>
        rw [show ([a] : List Digest).length = 1 from rfl, rootFromPath_one] at h
        simp only [MTHh_singleton, Option.some.injEq] at h
        have : i = 0 := by simp at hi; omega
        subst this
        exact Or.inl (by simp [h])
      | cons p rest =>
        rw [show ([a] : List Digest).length = 1 from rfl, rootFromPath_one_cons] at h
        exact absurd h (by simp)
    · have h2 : 2 ≤ hs.length := by omega
      cases path with
      | nil => rw [rootFromPath_nil M leafH h2] at h; exact absurd h (by simp)
      | cons p rest =>
        rw [rootFromPath_cons M leafH h2, MTHh_eq_node M h2] at h
        have hk : splitPoint hs.length < hs.length := splitPoint_lt h2
        have hkpos : 0 < splitPoint hs.length := splitPoint_pos hs.length
        by_cases hik : i < splitPoint hs.length
        · rw [if_pos hik] at h
          obtain ⟨a, ha, hnode⟩ := Option.map_eq_some_iff.mp h
          rcases node_eq_or_collision M hnode with ⟨hal, _⟩ | hc
          · subst hal
            have hlt : (hs.take (splitPoint hs.length)).length = splitPoint hs.length := by
              simp only [List.length_take]; omega
            rcases ih (hs.take (splitPoint hs.length)) leafH i rest
                (by omega) (by omega) (by rw [hlt]; exact ha) with hres | hc
            · refine Or.inl ?_
              rw [← hres, List.getElem?_take, if_pos hik]
            · exact Or.inr hc
          · exact Or.inr hc
        · rw [if_neg hik] at h
          obtain ⟨a, ha, hnode⟩ := Option.map_eq_some_iff.mp h
          rcases node_eq_or_collision M hnode with ⟨_, har⟩ | hc
          · subst har
            have hlt : (hs.drop (splitPoint hs.length)).length =
                hs.length - splitPoint hs.length := by simp only [List.length_drop]
            rcases ih (hs.drop (splitPoint hs.length)) leafH (i - splitPoint hs.length) rest
                (by omega) (by omega) (by rw [hlt]; exact ha) with hres | hc
            · refine Or.inl ?_
              rw [List.getElem?_drop] at hres
              rw [← hres]
              congr 1
              omega
            · exact Or.inr hc
          · exact Or.inr hc

/-- **Lemma 3b (inclusion soundness, under CR).** A verifying inclusion proof for `leaf` at
index `i` against the root of a leaf list `L` shows that `leaf` really is `L`'s `i`-th entry —
or exhibits a collision of `H`. -/
theorem inclusion_sound (M : HashModel Key) {L : List Bytes} {leaf : Bytes} {i : Nat}
    {path : List Digest} (hi : i < L.length)
    (h : verifyInclusion M leaf i L.length (MTH M L) path) :
    L[i]? = some leaf ∨ ∃ x y, Collision M.H x y := by
  have hmap : (L.map (leafHash M)).length = L.length := List.length_map _
  rcases inclusion_sound_aux M (L.map (leafHash M)).length (L.map (leafHash M))
      (leafHash M leaf) i path.reverse (Nat.le_refl _) (by omega)
      (by rw [hmap]; exact h) with hres | hc
  · rw [List.getElem?_map] at hres
    obtain ⟨a, ha, hleaf⟩ := Option.map_eq_some_iff.mp hres
    rcases leaf_eq_or_collision M hleaf with rfl | hc
    · exact Or.inl ha
    · exact Or.inr hc
  · exact Or.inr hc

/-! ## Lemma 3a — consistency soundness

Page: «Если `Consistent(m, n, MTH(L_m), MTH(L_n), π) = true`, то `L_m` — префикс `L_n`, либо
найдена коллизия `H`. Это и есть "append-only внутри показанного вида" (§8.3).» -/

theorem consistencyRoots_self (M : HashModel Key) (s : Digest) (m : Nat) (b : Bool)
    (proof : List Digest) :
    consistencyRoots M s m m b proof =
      (match b, proof with
        | true, [] => some (s, s)
        | false, [x] => some (x, x)
        | _, _ => none) := by
  rw [consistencyRoots.eq_def, dif_pos rfl]
  rfl

theorem consistencyRoots_step (M : HashModel Key) (s : Digest) {m n : Nat} (b : Bool)
    (hmn : m < n) (hm : 0 < m) (p : Digest) (rest : List Digest) :
    consistencyRoots M s m n b (p :: rest) =
      if m ≤ splitPoint n then
        (consistencyRoots M s m (splitPoint n) b rest).map fun rs => (rs.1, nodeHash M rs.2 p)
      else
        (consistencyRoots M s (m - splitPoint n) (n - splitPoint n) false rest).map fun rs =>
          (nodeHash M p rs.1, nodeHash M p rs.2) := by
  have h1 : ¬ (m = n) := by omega
  rw [consistencyRoots.eq_def, dif_neg h1, dif_pos (⟨hmn, hm⟩ : m < n ∧ 0 < m)]

theorem consistencyRoots_step_nil (M : HashModel Key) (s : Digest) {m n : Nat} (b : Bool)
    (hmn : m < n) (hm : 0 < m) : consistencyRoots M s m n b [] = none := by
  have h1 : ¬ (m = n) := by omega
  rw [consistencyRoots.eq_def, dif_neg h1, dif_pos (⟨hmn, hm⟩ : m < n ∧ 0 < m)]

/-- `MTH` of a list of two or more entries, unfolded at the RFC 9162 split. -/
theorem MTH_eq_node (M : HashModel Key) {L : List Bytes} (h : 2 ≤ L.length) :
    MTH M L =
      nodeHash M (MTH M (L.take (splitPoint L.length))) (MTH M (L.drop (splitPoint L.length))) := by
  have hlen : (L.map (leafHash M)).length = L.length := List.length_map _
  simp only [MTH]
  rw [MTHh_eq_node M (by omega : 2 ≤ (L.map (leafHash M)).length)]
  simp only [hlen, List.map_take, List.map_drop]

theorem consistency_sound_aux (M : HashModel Key) :
    ∀ (N : Nat) (Lm Ln : List Bytes) (m n : Nat) (b : Bool) (seed : Digest)
      (proof : List Digest),
      n ≤ N → Lm.length = m → Ln.length = n → 0 < m → m ≤ n →
      (b = true → seed = MTH M Lm) →
      consistencyRoots M seed m n b proof = some (MTH M Lm, MTH M Ln) →
      Lm = Ln.take m ∨ ∃ x y, Collision M.H x y := by
  intro N
  induction N with
  | zero => intro _ _ m n _ _ _ hle _ _ hm hmn _ _; exact False.elim (by omega)
  | succ N ih =>
    intro Lm Ln m n b seed proof hle hlm hln hm hmn hb h
    by_cases heqmn : m = n
    · subst heqmn
      have hroots : MTH M Lm = MTH M Ln := by
        rw [consistencyRoots_self] at h
        cases b with
        | true =>
          cases proof with
          | nil =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1, ← h.2]
          | cons _ _ => exact absurd h (by simp)
        | false =>
          match proof, h with
          | [x], h =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rw [← h.1, ← h.2]
          | [], h => exact absurd h (by simp)
          | _ :: _ :: _, h => exact absurd h (by simp)
      rcases mth_inj_or_collision M (by omega) hroots with rfl | hc
      · exact Or.inl (by rw [List.take_of_length_le (by omega)])
      · exact Or.inr hc
    · have hlt : m < n := by omega
      have hn2 : 2 ≤ n := by omega
      have hk : splitPoint n < n := splitPoint_lt hn2
      have hkpos : 0 < splitPoint n := splitPoint_pos n
      cases proof with
      | nil => rw [consistencyRoots_step_nil M seed b hlt hm] at h; exact absurd h (by simp)
      | cons p rest =>
        rw [consistencyRoots_step M seed b hlt hm] at h
        rw [MTH_eq_node M (by omega : 2 ≤ Ln.length)] at h
        by_cases hmk : m ≤ splitPoint n
        · rw [if_pos hmk] at h
          obtain ⟨rs, hrs, heq⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨r1, r2⟩ := rs
          simp only [Prod.mk.injEq] at heq
          rcases node_eq_or_collision M heq.2 with ⟨hl, _⟩ | hc
          · have hlnk : (Ln.take (splitPoint n)).length = splitPoint n := by
              simp only [List.length_take]; omega
            have hrec : consistencyRoots M seed m (splitPoint n) b rest =
                some (MTH M Lm, MTH M (Ln.take (splitPoint Ln.length))) := by
              rw [hrs, heq.1, hl]
            rw [hln] at hrec
            rcases ih Lm (Ln.take (splitPoint n)) m (splitPoint n) b seed rest
                (by omega) hlm hlnk hm hmk hb hrec with hpre | hc
            · refine Or.inl ?_
              rw [hpre, List.take_take]
              congr 1
              omega
            · exact Or.inr hc
          · exact Or.inr hc
        · rw [if_neg hmk] at h
          have hm2 : 2 ≤ m := by omega
          have hsp : splitPoint m = splitPoint n := splitPoint_eq_of_gt hm2 hmn (by omega)
          rw [MTH_eq_node M (by omega : 2 ≤ Lm.length)] at h
          obtain ⟨rs, hrs, heq⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨r1, r2⟩ := rs
          simp only [Prod.mk.injEq] at heq
          rcases node_eq_or_collision M heq.1 with ⟨hpm, hrm⟩ | hc
          · rcases node_eq_or_collision M heq.2 with ⟨hpn, hrn⟩ | hc
            · have hprefix : MTH M (Lm.take (splitPoint n)) = MTH M (Ln.take (splitPoint n)) := by
                rw [hlm, hsp] at hpm
                rw [hln] at hpn
                rw [← hpm, ← hpn]
              have hlenm : (Lm.take (splitPoint n)).length = splitPoint n := by
                simp only [List.length_take]; omega
              have hlenn : (Ln.take (splitPoint n)).length = splitPoint n := by
                simp only [List.length_take]; omega
              rcases mth_inj_or_collision M (by omega) hprefix with hheads | hc
              · have hlmd : (Lm.drop (splitPoint n)).length = m - splitPoint n := by
                  simp only [List.length_drop]; omega
                have hlnd : (Ln.drop (splitPoint n)).length = n - splitPoint n := by
                  simp only [List.length_drop]; omega
                have hrec : consistencyRoots M seed (m - splitPoint n) (n - splitPoint n) false
                    rest = some (MTH M (Lm.drop (splitPoint n)), MTH M (Ln.drop (splitPoint n))) := by
                  rw [hrs]
                  rw [hlm, hsp] at hrm
                  rw [hln] at hrn
                  rw [hrm, hrn]
                rcases ih (Lm.drop (splitPoint n)) (Ln.drop (splitPoint n)) (m - splitPoint n)
                    (n - splitPoint n) false seed rest (by omega) hlmd hlnd (by omega)
                    (by omega) (by simp) hrec with htails | hc
                · refine Or.inl ?_
                  calc Lm = Lm.take (splitPoint n) ++ Lm.drop (splitPoint n) :=
                        (List.take_append_drop _ _).symm
                    _ = Ln.take (splitPoint n) ++ (Ln.drop (splitPoint n)).take (m - splitPoint n) := by
                        rw [hheads, htails]
                    _ = Ln.take m := by
                        have hsplit : Ln.take (splitPoint n + (m - splitPoint n)) =
                            Ln.take (splitPoint n) ++
                              (Ln.drop (splitPoint n)).take (m - splitPoint n) :=
                          take_add' _ _ _
                        rw [show splitPoint n + (m - splitPoint n) = m from by omega] at hsplit
                        exact hsplit.symm
                · exact Or.inr hc
              · exact Or.inr hc
            · exact Or.inr hc
          · exact Or.inr hc

/-- **Lemma 3a (consistency soundness, under CR).** A verifying RFC 9162 consistency proof from
`(m, MTH(L_m))` to `(n, MTH(L_n))` shows that `L_m` is the size-`m` prefix of `L_n` — the
append-only property "within the view shown to the verifier" (I-D Section 8.3) — or exhibits a
collision of `H`. -/
theorem consistency_sound (M : HashModel Key) {Lm Ln : List Bytes} {proof : List Digest}
    (hpos : 0 < Lm.length) (hmn : Lm.length ≤ Ln.length)
    (h : verifyConsistency M Lm.length Ln.length (MTH M Lm) (MTH M Ln) proof) :
    Lm = Ln.take Lm.length ∨ ∃ x y, Collision M.H x y :=
  consistency_sound_aux M Ln.length Lm Ln Lm.length Ln.length true (MTH M Lm) proof.reverse
    (Nat.le_refl _) rfl rfl hpos hmn (fun _ => rfl) h

/-! ## Lemma 3c — enumeration soundness

Page: «`Range(i, j, n, MTH(L_n), E, π) = true` → `E = L_n[i..j)` поэлементно и по порядку.
Именно это делает `S_C` леммы 2 полным префиксом ("know that nothing was skipped", §3.1 п. 5).» -/

theorem rangeRoot_outside (M : HashModel Key) (fr to : Nat) (E : List Bytes)
    (offset size : Nat) (nodes : List Digest) (h : classify offset size fr to = .outside) :
    rangeRoot M fr to E offset size nodes =
      (match nodes with | [] => none | p :: rest => some (p, rest)) := by
  rw [rangeRoot.eq_def, h]
  rfl

theorem rangeRoot_inside (M : HashModel Key) (fr to : Nat) (E : List Bytes)
    (offset size : Nat) (nodes : List Digest) (h : classify offset size fr to = .inside) :
    rangeRoot M fr to E offset size nodes =
      some (MTH M ((E.drop (offset - fr)).take size), nodes) := by
  rw [rangeRoot.eq_def, h]

theorem rangeRoot_straddles (M : HashModel Key) (fr to : Nat) (E : List Bytes)
    {offset size : Nat} (nodes : List Digest) (h : classify offset size fr to = .straddles)
    (h2 : 2 ≤ size) :
    rangeRoot M fr to E offset size nodes =
      (match rangeRoot M fr to E offset (splitPoint size) nodes with
        | none => none
        | some (l, rest) =>
          match rangeRoot M fr to E (offset + splitPoint size) (size - splitPoint size) rest with
          | none => none
          | some (r, rest') => some (nodeHash M l r, rest')) := by
  have h0 : ¬ (size = 0) := by omega
  have h1 : ¬ (size = 1) := by omega
  rw [rangeRoot.eq_def, h, dif_neg h0, dif_neg h1]
  rfl

theorem range_sound_aux (M : HashModel Key) :
    ∀ (N : Nat) (L E : List Bytes) (fr to offset size : Nat) (nodes rest : List Digest)
      (d : Digest),
      size ≤ N → offset + size ≤ L.length → E.length = to - fr → fr < to →
      rangeRoot M fr to E offset size nodes = some (d, rest) →
      d = MTH M ((L.drop offset).take size) →
      (∀ i, fr ≤ i → i < to → offset ≤ i → i < offset + size → E[i - fr]? = L[i]?)
        ∨ ∃ x y, Collision M.H x y := by
  intro N
  induction N with
  | zero =>
    intro _ _ _ to offset size _ _ _ hle _ _ _ _ _
    exact Or.inl (fun i _ _ _ h4 => False.elim (by omega))
  | succ N ih =>
    intro L E fr to offset size nodes rest d hle hL hE hfr hrun hd
    match hcl : classify offset size fr to with
    | .outside =>
      refine Or.inl (fun i h1 h2 h3 h4 => ?_)
      simp only [classify] at hcl
      split at hcl
      · exact False.elim (by omega)
      · split at hcl <;> simp at hcl
    | .inside =>
      rw [rangeRoot_inside M fr to E offset size nodes hcl] at hrun
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      have hin : fr ≤ offset ∧ offset + size ≤ to := by
        simp only [classify] at hcl
        split at hcl
        · simp at hcl
        · split at hcl
          · next hcond => exact hcond
          · simp at hcl
      have hlenE : ((E.drop (offset - fr)).take size).length = size := by
        simp only [List.length_take, List.length_drop]; omega
      have hlenL : ((L.drop offset).take size).length = size := by
        simp only [List.length_take, List.length_drop]; omega
      rcases mth_inj_or_collision M (by omega) (hrun.1 ▸ hd : MTH M ((E.drop (offset - fr)).take size)
          = MTH M ((L.drop offset).take size)) with heq | hc
      · refine Or.inl (fun i h1 h2 h3 h4 => ?_)
        have := congrArg (fun l => l[i - offset]?) heq
        simp only [List.getElem?_take, List.getElem?_drop] at this
        rw [if_pos (by omega), if_pos (by omega)] at this
        rw [show offset - fr + (i - offset) = i - fr from by omega,
          show offset + (i - offset) = i from by omega] at this
        exact this
      · exact Or.inr hc
    | .straddles =>
      by_cases h2 : 2 ≤ size
      · rw [rangeRoot_straddles M fr to E nodes hcl h2] at hrun
        have hk : splitPoint size < size := splitPoint_lt h2
        have hkpos : 0 < splitPoint size := splitPoint_pos size
        cases hleft : rangeRoot M fr to E offset (splitPoint size) nodes with
        | none => rw [hleft] at hrun; exact absurd hrun (by simp)
        | some res1 =>
          obtain ⟨l, rest1⟩ := res1
          rw [hleft] at hrun
          simp only at hrun
          cases hright : rangeRoot M fr to E (offset + splitPoint size) (size - splitPoint size)
              rest1 with
          | none => rw [hright] at hrun; exact absurd hrun (by simp)
          | some res2 =>
            obtain ⟨r, rest2⟩ := res2
            rw [hright] at hrun
            simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            have hlenL : ((L.drop offset).take size).length = size := by
              simp only [List.length_take, List.length_drop]; omega
            rw [MTH_eq_node M (by omega : 2 ≤ ((L.drop offset).take size).length), hlenL] at hd
            have hLeft : ((L.drop offset).take size).take (splitPoint size)
                = (L.drop offset).take (splitPoint size) := by
              rw [List.take_take, Nat.min_eq_left (by omega)]
            have hRight : ((L.drop offset).take size).drop (splitPoint size)
                = (L.drop (offset + splitPoint size)).take (size - splitPoint size) := by
              rw [drop_take', List.drop_drop]
            rw [hLeft, hRight] at hd
            rcases node_eq_or_collision M (hrun.1 ▸ hd : nodeHash M l r
                = nodeHash M (MTH M ((L.drop offset).take (splitPoint size)))
                    (MTH M ((L.drop (offset + splitPoint size)).take (size - splitPoint size))))
              with ⟨hl, hr⟩ | hc
            · rcases ih L E fr to offset (splitPoint size) nodes rest1 l (by omega) (by omega)
                  hE hfr hleft hl with hgl | hc
              · rcases ih L E fr to (offset + splitPoint size) (size - splitPoint size) rest1
                    rest2 r (by omega) (by omega) hE hfr hright hr with hgr | hc
                · refine Or.inl (fun i h1 h2 h3 h4 => ?_)
                  by_cases hsplit : i < offset + splitPoint size
                  · exact hgl i h1 h2 h3 hsplit
                  · exact hgr i h1 h2 (by omega) (by omega)
                · exact Or.inr hc
              · exact Or.inr hc
            · exact Or.inr hc
      · exfalso
        rw [rangeRoot.eq_def, hcl] at hrun
        by_cases h0 : size = 0
        · rw [dif_pos h0] at hrun; exact absurd hrun (by simp)
        · rw [dif_neg h0, dif_pos (by omega : size = 1)] at hrun
          exact absurd hrun (by simp)

/-- **Lemma 3c (enumeration soundness, under CR).** A verifying authenticated range proof over
`[from, to)` against the checkpoint root shows the carried entries ARE the log's entries at
those indexes, in order — or exhibits a collision of `H`. This is what makes the corpus `S_C`
of Lemma 2 a complete prefix: "know that nothing was skipped" (I-D Section 3.1 item 5). -/
theorem range_sound (M : HashModel Key) {L E : List Bytes} {fr to n : Nat} {nodes : List Digest}
    (hL : L.length = n) (h : verifyRange M fr to n (MTH M L) E nodes) :
    E = (L.take to).drop fr ∨ ∃ x y, Collision M.H x y := by
  obtain ⟨hfr, hton, hE, hrun⟩ := h
  have hd : MTH M L = MTH M ((L.drop 0).take n) := by
    simp only [List.drop_zero]
    rw [List.take_of_length_le (by omega)]
  rcases range_sound_aux M n L E fr to 0 n nodes [] (MTH M L) (Nat.le_refl _) (by omega) hE hfr
      hrun hd with hpoint | hc
  · refine Or.inl (List.ext_getElem? fun j => ?_)
    by_cases hj : j < to - fr
    · have := hpoint (fr + j) (by omega) (by omega) (by omega) (by omega)
      rw [show fr + j - fr = j from by omega] at this
      rw [this, List.getElem?_drop, List.getElem?_take, if_pos (by omega)]
    · have h1 : E[j]? = none := by
        rw [List.getElem?_eq_none_iff]; omega
      have h2 : ((L.take to).drop fr)[j]? = none := by
        rw [List.getElem?_eq_none_iff]
        simp only [List.length_drop, List.length_take]
        omega
      rw [h1, h2]
  · exact Or.inr hc

/-! ## Lemma 3d — the composition of Lemmas 2 and 3

Page: «При `Consistent(C → C')` и `Range` под `C` и `C'`: `affected(t, C) ⊆ affected(t, C')` —
то есть лемма 2c получает своё условие из 3a.»

The bridge between the two developments is a parameter, not a definition: this model does not
parse an anchored envelope into a statement.

-- AMBIGUITY: the invariants page's model for Lemma 2 is a log of statements and the model for
-- Lemma 3 is a log of opaque octet strings (I-D Section 3.1 item 1: "entries treated as opaque
-- bytes"). Nothing in either document says how one becomes the other — that is JSON parsing,
-- which both models exclude. `decode : Bytes → Entry V` is therefore a parameter of the two
-- composition theorems, and they hold for any decoder: what they show is that the closure
-- depends only on the entry bytes the log commits, whatever those bytes are taken to mean. -/

/-- **Lemma 3d, first half.** A verifying consistency proof from the checkpoint `C` to the
checkpoint `C'` supplies exactly the hypothesis Lemma 2c needs: the corpus under `C` is a
prefix of the corpus under `C'`, so the affected set at `C` is contained in the affected set at
`C'` — or a collision of `H` has been exhibited. -/
theorem affected_mono_of_consistency {V : Type} (M : HashModel Key) (decode : Bytes → Entry V)
    {Lm Ln : List Bytes} {t : Nat} {proof : List Digest} {r : RecordRef}
    (hpos : 0 < Lm.length) (hmn : Lm.length ≤ Ln.length)
    (hcons : verifyConsistency M Lm.length Ln.length (MTH M Lm) (MTH M Ln) proof)
    (h : Affected (Lm.map decode) Lm.length t r) :
    Affected (Ln.map decode) Ln.length t r ∨ ∃ x y, Collision M.H x y := by
  rcases consistency_sound M hpos hmn hcons with hprefix | hc
  · refine Or.inl ?_
    have hlenm : (Lm.map decode).length = Lm.length := List.length_map _
    have hpre : (Lm.map decode).take Lm.length = (Ln.map decode).take Lm.length := by
      rw [List.take_of_length_le (by omega), ← List.map_take, ← hprefix]
    have heq := affected_of_prefix_eq (V := V) (log₁ := Lm.map decode) (log₂ := Ln.map decode)
      (n := Lm.length) (t := t) h.1 hpre
    have hmid : Affected (Ln.map decode) Lm.length t r := by rw [← heq]; exact h
    exact affected_mono (by simpa only [List.length_map] using hmn) hmid
  · exact Or.inr hc

/-- **Lemma 3d, second half.** An authenticated enumeration of the whole prefix a checkpoint
commits carries the log's own entries, so the closure a verifier computes from the enumeration
is the closure over the log's true prefix — or a collision of `H` has been exhibited. This is
the step that turns Lemma 2 from a statement about a computation into a statement about the
corpus (invariants page Section 2, «Граница»; I-D Section 3.1 item 5). -/
theorem enumerated_closure_eq {V : Type} (M : HashModel Key) (decode : Bytes → Entry V)
    {L E : List Bytes} {n t : Nat} {nodes : List Digest}
    (hL : L.length = n) (h : verifyRange M 0 n n (MTH M L) E nodes) :
    Affected (E.map decode) n t = Affected (L.map decode) n t ∨ ∃ x y, Collision M.H x y := by
  rcases range_sound M hL h with hE | hc
  · refine Or.inl ?_
    rw [hE, List.drop_zero, List.take_of_length_le (by omega)]
  · exact Or.inr hc

/-! ## Non-vacuity

The soundness lemmas would hold vacuously if no proof ever verified. These two examples show
the verifier accepting genuine inclusion proofs, and pin the `splitPoint` arithmetic. -/

/-- A one-leaf tree: the empty path opens the root. -/
example (M : HashModel Key) (b : Bytes) : verifyInclusion M b 0 1 (MTH M [b]) [] := by
  simp only [verifyInclusion, List.reverse_nil, rootFromPath_one, MTH, List.map_cons,
    List.map_nil, MTHh_singleton]

/-- A two-leaf tree: the sibling leaf hash opens the root for the left leaf. -/
example (M : HashModel Key) (a b : Bytes) :
    verifyInclusion M a 0 2 (MTH M [a, b]) [leafHash M b] := by
  have hsplit : splitPoint 2 = 1 := rfl
  simp only [verifyInclusion, List.reverse_cons, List.reverse_nil, List.nil_append]
  rw [rootFromPath_cons M (leafHash M a) (by omega) (leafHash M b) [], hsplit, if_pos (by omega),
    rootFromPath_one, MTH_eq_node M (by simp)]
  simp only [Option.map_some, List.length_cons, List.length_nil, hsplit, List.take_succ_cons,
    List.take_zero, List.drop_succ_cons, List.drop_zero, MTH, List.map_cons, List.map_nil,
    MTHh_singleton]

end AhlProofs.Tree
