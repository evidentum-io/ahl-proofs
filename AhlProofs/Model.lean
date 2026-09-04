/-!
# The abstract model (AHL invariants page, Section 0)

This module fixes the model over which the AHL lemmas are stated. It deliberately knows
nothing about JSON, about the wire format, or about any implementation: octets, digests, a
hash and a keyed hash as *abstract functions*, and the commitment preimage encoding of the
AHL I-D (revision 0.4) Section 2.6.

Two conventions carry the honesty requirement of the invariants page:

* Every cryptographic assumption is a **parameter** — a field of `HashModel` or
  `DescriptorModel` — never a global `axiom`. Nothing here is asserted about the real
  SHA-256.
* Collision resistance is **never** stated as injectivity of `H`. A fixed-width function over
  unbounded inputs is not injective (I-D Section 2.6, last paragraphs), so the lemmas below
  conclude `Collision` — an exhibited pair `a ≠ b` with `H a = H b` — and the informal CR
  assumption (I-D Section 8.1) is exactly the claim that producing such a pair is infeasible.
  That assumption is not, and cannot be, a Lean hypothesis: it is a statement about
  adversaries, not about functions.
-/

namespace AhlProofs

/-- Octet strings. The model's only concrete datatype (invariants page Section 0). -/
abbrev Bytes := List UInt8

/-- The commitment preimage separator `0x1F` (I-D Section 2.6; `ahl-core`
`DATASET_SEPARATOR`). The two occurrences in a preimage are literal separators. -/
def SEP : UInt8 := 0x1F

/-- A digest: exactly 32 octets (I-D Section 2.6, "taken as the raw 32 digest octets, not as
a family string"). -/
structure Digest where
  /-- The 32 raw digest octets. -/
  octets : Bytes
  /-- The width of a SHA-256 / HMAC-SHA-256 digest. -/
  length_eq : octets.length = 32

/-- Digests are determined by their octets: the length field is a proposition. -/
theorem Digest.eq_of_octets_eq {d e : Digest} (h : d.octets = e.octets) : d = e := by
  cases d
  cases e
  simp only at h
  subst h
  rfl

/-- Well-formedness of a dataset id (I-D Section 2.6, "Dataset id syntax and encoding" and the
control-octet prohibition; `ahl-core` `descriptor::validate_dataset_id`): at least 1 and at
most 128 octets, each printable US-ASCII in `0x21..=0x7E`. -/
def WF (dsid : Bytes) : Prop :=
  1 ≤ dsid.length ∧ dsid.length ≤ 128 ∧ ∀ o ∈ dsid, 33 ≤ o.toNat ∧ o.toNat ≤ 126

/-- The consequence of `WF` that the preimage parsing argument actually uses: a well-formed
dataset id contains no `0x1F`. The I-D states the control-octet prohibition as its own
normative requirement for exactly this reason (Section 2.6). -/
theorem WF.sep_not_mem {dsid : Bytes} (h : WF dsid) : SEP ∉ dsid := by
  intro hmem
  have hrange := h.2.2 SEP hmem
  have hsep : SEP.toNat = 31 := by decide
  omega

/-- The commitment preimage `dsid || 0x1F || ddig || 0x1F || canonical bytes`
(I-D Section 2.6; `ahl-core` `commitment_input`). -/
def pre (dsid : Bytes) (ddig : Digest) (b : Bytes) : Bytes :=
  dsid ++ SEP :: (ddig.octets ++ SEP :: b)

/-- An exhibited collision of `f`: a pair of distinct inputs with one output.

This is the *conclusion* of the binding lemmas, never a hypothesis. The CR assumption of
I-D Section 8.1 says such a pair cannot feasibly be produced; a verifier that observes the
premises of Lemma 1b therefore holds a witness against that assumption. -/
def Collision {α : Type} (f : Bytes → α) (a b : Bytes) : Prop :=
  a ≠ b ∧ f a = f b

/-- The hash primitives of I-D Section 2.6, as parameters.

`H` stands for SHA-256 and `HMAC k` for HMAC-SHA-256 under the dataset key `k`. No property
whatsoever is assumed of either: the lemmas hold for *any* functions of these types, which is
why they cannot be stronger than the CR assumption they are read against (I-D Section 8.1). -/
structure HashModel (Key : Type) where
  /-- The unkeyed digest function (SHA-256 in this revision, I-D Section 8.1). -/
  H : Bytes → Digest
  /-- The keyed digest function (HMAC-SHA-256, I-D Section 2.6, `keyed` mode). -/
  HMAC : Key → Bytes → Digest

/-- `plain` commitment: `SHA-256(dsid || 0x1F || ddig || 0x1F || canonical bytes)`
(I-D Section 2.6; `ahl-core` `commit_plain`). -/
def HashModel.commit_plain {Key : Type} (M : HashModel Key)
    (dsid : Bytes) (ddig : Digest) (b : Bytes) : Digest :=
  M.H (pre dsid ddig b)

/-- `keyed` commitment: `HMAC-SHA-256(k_dataset, dsid || 0x1F || ddig || 0x1F || canonical
bytes)` (I-D Section 2.6; `ahl-core` `commit_keyed`). -/
def HashModel.commit_keyed {Key : Type} (M : HashModel Key) (k : Key)
    (dsid : Bytes) (ddig : Digest) (b : Bytes) : Digest :=
  M.HMAC k (pre dsid ddig b)

/-- The canonicalization descriptor side of the model (I-D Section 2.6, `ddig = SHA-256(JCS(D))`).

`Desc` is the type of canonicalization descriptors `{canonicalization, media_type?}`; the
model does not describe their structure, only that they are canonically encoded by `JCS`. -/
structure DescriptorModel (Desc : Type) where
  /-- RFC 8785 canonical encoding of a descriptor. -/
  JCS : Desc → Bytes
  /-- **Assumption JCS-INJ** (invariants page Section 0; I-D Section 2.6): RFC 8785
  canonicalization is injective on I-JSON values — one canonical encoding is produced by at
  most one descriptor. Declared as an assumption rather than proved: the AHL documents say so
  explicitly, and nothing here strengthens it. Lemma 1c uses it through
  `DescriptorModel.jcs_ne`, the contrapositive. -/
  jcs_inj : Function.Injective JCS

/-- The contrapositive of JCS-INJ, which is the form Lemma 1c consumes: distinct descriptors
have distinct canonical encodings. -/
theorem DescriptorModel.jcs_ne {Desc : Type} (Dm : DescriptorModel Desc) {D₁ D₂ : Desc}
    (h : D₁ ≠ D₂) : Dm.JCS D₁ ≠ Dm.JCS D₂ :=
  fun he => h (Dm.jcs_inj he)

/-- The descriptor digest `ddig = H(JCS(D))` (I-D Section 2.6). -/
def HashModel.ddig {Key Desc : Type} (M : HashModel Key) (Dm : DescriptorModel Desc)
    (D : Desc) : Digest :=
  M.H (Dm.JCS D)

end AhlProofs
