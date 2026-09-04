import AhlProofs.Model

/-!
# Lemma 1 — record binding (AHL invariants page, Section 1)

Source: AHL I-D revision 0.4, Section 2.6 (the paragraphs on preimage injectivity),
Section 8.1 (the collision-resistance assumption), Section 8.6 (descriptor binding —
"detection, not disclosure").

* **Lemma 1a** (`preimage_injective`) is unconditional and constructive: the preimage encoding
  is injective over the triple `(dsid, ddig, canonical bytes)` "by parsing alone".
* **Lemma 1b** (`commit_plain_collision`, `commit_keyed_collision`) turns an equal commitment
  over distinct well-formed triples into an exhibited collision of `H` (resp. `HMAC k`).
* **Lemma 1c** (`descriptor_digest_collision`, `commit_plain_descriptor_collision`) covers the
  step the I-D marks as *not* unconditional: distinct descriptors yield distinct `ddig` only
  under CR, so an equal `ddig` over distinct descriptors is again an exhibited collision.

Nothing here assumes the absence of collisions; see `AhlProofs.Model.Collision`.
-/

namespace AhlProofs

/-! ## Two list facts used by the parsing argument -/

/-- Splitting at a separator that occurs in neither prefix: if `a ++ s :: b = c ++ s :: d` and
`s` occurs in neither `a` nor `c`, then the two splits coincide.

This is the formal content of "the FIRST `0x1F` in the preimage always ends `dsid`"
(I-D Section 2.6). -/
theorem split_at_first_sep {α : Type} {s : α} :
    ∀ {a b c d : List α}, a ++ s :: b = c ++ s :: d → s ∉ a → s ∉ c → a = c ∧ b = d := by
  intro a
  induction a with
  | nil =>
    intro b c d h _ hc
    cases c with
    | nil => exact ⟨rfl, by simpa using h⟩
    | cons y c' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) hc
  | cons x a' ih =>
    intro b c d h ha hc
    cases c with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) ha
    | cons y c' =>
      simp only [List.cons_append, List.cons.injEq] at h
      have ha' : s ∉ a' := fun hm => ha (List.mem_cons_of_mem x hm)
      have hc' : s ∉ c' := fun hm => hc (List.mem_cons_of_mem y hm)
      obtain ⟨hle, hre⟩ := ih h.2 ha' hc'
      exact ⟨by rw [h.1, hle], hre⟩

/-! ## Lemma 1a — unconditional preimage injectivity -/

/-- **Lemma 1a** (unconditional, by parsing alone; I-D Section 2.6).

Over well-formed dataset ids the commitment preimage determines the triple
`(dsid, ddig, canonical bytes)`. No cryptographic assumption is used: the first `0x1F` ends
`dsid` because a well-formed dataset id contains none, `ddig` is then exactly 32 octets, the
octet after it is the second `0x1F`, and everything following is the canonical bytes. -/
theorem preimage_injective {dsid₁ dsid₂ b₁ b₂ : Bytes} {ddig₁ ddig₂ : Digest}
    (h₁ : WF dsid₁) (h₂ : WF dsid₂)
    (h : pre dsid₁ ddig₁ b₁ = pre dsid₂ ddig₂ b₂) :
    dsid₁ = dsid₂ ∧ ddig₁ = ddig₂ ∧ b₁ = b₂ := by
  obtain ⟨hdsid, hrest⟩ := split_at_first_sep h h₁.sep_not_mem h₂.sep_not_mem
  obtain ⟨hoct, htail⟩ :=
    List.append_inj hrest (by rw [ddig₁.length_eq, ddig₂.length_eq])
  exact ⟨hdsid, Digest.eq_of_octets_eq hoct, by simpa using htail⟩

/-- Contrapositive of Lemma 1a, in the form Lemma 1b consumes: distinct well-formed triples
have distinct preimages. -/
theorem preimage_ne {dsid₁ dsid₂ b₁ b₂ : Bytes} {ddig₁ ddig₂ : Digest}
    (h₁ : WF dsid₁) (h₂ : WF dsid₂)
    (hne : ¬(dsid₁ = dsid₂ ∧ ddig₁ = ddig₂ ∧ b₁ = b₂)) :
    pre dsid₁ ddig₁ b₁ ≠ pre dsid₂ ddig₂ b₂ :=
  fun h => hne (preimage_injective h₁ h₂ h)

/-! ## Lemma 1b — equal commitments over distinct triples exhibit a collision -/

section Commitments

variable {Key : Type} (M : HashModel Key)

/-- **Lemma 1b**, `plain` mode (I-D Section 2.6, Section 8.1).

If two distinct well-formed triples receive the same `plain` commitment, the two preimages are
a collision of `H`. Read against the CR assumption of Section 8.1: this situation cannot
feasibly arise, and if it does the observer holds the witness. -/
theorem commit_plain_collision {dsid₁ dsid₂ b₁ b₂ : Bytes} {ddig₁ ddig₂ : Digest}
    (h₁ : WF dsid₁) (h₂ : WF dsid₂)
    (hne : ¬(dsid₁ = dsid₂ ∧ ddig₁ = ddig₂ ∧ b₁ = b₂))
    (heq : M.commit_plain dsid₁ ddig₁ b₁ = M.commit_plain dsid₂ ddig₂ b₂) :
    Collision M.H (pre dsid₁ ddig₁ b₁) (pre dsid₂ ddig₂ b₂) :=
  ⟨preimage_ne h₁ h₂ hne, heq⟩

/-- **Lemma 1b**, `keyed` mode (I-D Section 2.6, `keyed`; Section 8.1).

Same statement for `HMAC k` at a fixed dataset key. The I-D reduces CR of HMAC-SHA-256 under a
known key to CR of SHA-256; that reduction is outside this model, so the conclusion is stated
against `M.HMAC k` directly. -/
theorem commit_keyed_collision (k : Key) {dsid₁ dsid₂ b₁ b₂ : Bytes} {ddig₁ ddig₂ : Digest}
    (h₁ : WF dsid₁) (h₂ : WF dsid₂)
    (hne : ¬(dsid₁ = dsid₂ ∧ ddig₁ = ddig₂ ∧ b₁ = b₂))
    (heq : M.commit_keyed k dsid₁ ddig₁ b₁ = M.commit_keyed k dsid₂ ddig₂ b₂) :
    Collision (M.HMAC k) (pre dsid₁ ddig₁ b₁) (pre dsid₂ ddig₂ b₂) :=
  ⟨preimage_ne h₁ h₂ hne, heq⟩

end Commitments

/-! ## Lemma 1c — the descriptor step, which is not unconditional -/

section Descriptors

variable {Key Desc : Type} (M : HashModel Key) (Dm : DescriptorModel Desc)

/-- **Lemma 1c** (under CR and JCS-INJ; I-D Section 2.6, Section 8.6).

Distinct descriptors with one descriptor digest exhibit a collision of `H` on their canonical
encodings. The I-D is explicit that this step is conditional — "two distinct descriptors
sharing a `ddig` would share a preimage" — and the lemma repeats that rather than hiding it. -/
theorem descriptor_digest_collision {D₁ D₂ : Desc} (hne : D₁ ≠ D₂)
    (heq : M.ddig Dm D₁ = M.ddig Dm D₂) :
    Collision M.H (Dm.JCS D₁) (Dm.JCS D₂) :=
  ⟨Dm.jcs_inj D₁ D₂ hne, heq⟩

/-- **Lemma 1c**, composed with Lemma 1b: at the level of the triple
`(dataset id, descriptor, canonical bytes)` — the triple the I-D warns is *not* the one the
encoding is unconditionally injective over — an equal `plain` commitment over distinct
well-formed triples exhibits a collision of `H`, either on the two descriptor encodings or on
the two preimages. -/
theorem commit_plain_descriptor_collision {dsid₁ dsid₂ b₁ b₂ : Bytes} {D₁ D₂ : Desc}
    (h₁ : WF dsid₁) (h₂ : WF dsid₂)
    (hne : ¬(dsid₁ = dsid₂ ∧ D₁ = D₂ ∧ b₁ = b₂))
    (heq : M.commit_plain dsid₁ (M.ddig Dm D₁) b₁
         = M.commit_plain dsid₂ (M.ddig Dm D₂) b₂) :
    Collision M.H (Dm.JCS D₁) (Dm.JCS D₂) ∨
      Collision M.H (pre dsid₁ (M.ddig Dm D₁) b₁) (pre dsid₂ (M.ddig Dm D₂) b₂) := by
  by_cases hdig : M.ddig Dm D₁ = M.ddig Dm D₂
  · by_cases hD : D₁ = D₂
    · exact Or.inr
        ⟨preimage_ne h₁ h₂ (fun ht => hne ⟨ht.1, hD, ht.2.2⟩), heq⟩
    · exact Or.inl (descriptor_digest_collision M Dm hD hdig)
  · exact Or.inr ⟨preimage_ne h₁ h₂ (fun ht => hdig ht.2.1), heq⟩

end Descriptors

/-! ## Non-vacuity

Lemma 1a is stated over well-formed dataset ids, so the hypothesis must be inhabited: the
dataset id `scores` of the I-D's own examples (Section 2.6) satisfies `WF`. -/

/-- The US-ASCII octets of `scores`, the dataset id used in the I-D examples. -/
def scoresDsid : Bytes := [0x73, 0x63, 0x6F, 0x72, 0x65, 0x73]

example : WF scoresDsid := by
  unfold WF scoresDsid
  decide

end AhlProofs
