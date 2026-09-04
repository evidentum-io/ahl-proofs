import AhlProofs.Model

/-!
# The tree model (RFC 9162 geometry, AHL I-D Section 2.7)

The Merkle tree hash, inclusion paths, consistency proofs and the crate's authenticated range
proof, over the abstract model of the invariants page Section 0: `H : Bytes → Digest` is a
parameter (`AhlProofs.HashModel`, shared with Lemma 1), nothing is assumed about it, and
collisions are concluded rather than excluded.

Sources: RFC 9162 Section 2.1 (Merkle tree hash, inclusion proof, consistency proof); AHL I-D
revision 0.4 Section 2.7 (SHA-256 throughout; a leaf hashes as `SHA-256(0x00 || leaf)` and an
internal node as `SHA-256(0x01 || left || right)`); Section 3.1 items 3 and 5 (inclusion and
consistency proofs, authenticated enumeration); Section 7.4 (the range enumeration form);
`ahl-core/src/lib.rs` (`leaf_hash`, `tree_root`, `inclusion_proof`, `verify_inclusion_proof`,
`consistency_proof`, `verify_consistency_proof`) and `ahl-core/src/range_proof.rs`.

Two levels are kept apart, as the crate keeps them apart: `MTHh` is the tree hash over a list
of *leaf hashes* (`atl_core::core::merkle::compute_root`, which `ahl-core` delegates to), and
`MTH` is the tree hash over a list of *entries*, which applies `leafHash` first (`ahl-core`
`tree_root`).
-/

namespace AhlProofs.Tree

open AhlProofs

variable {Key : Type}

/-! ## The RFC 9162 split -/

/-- The largest power of two strictly less than `n`, for `n ≥ 2` — the RFC 9162 Section 2.1
split point (`atl_core::core::merkle::largest_power_of_2_less_than`). -/
def splitPoint (n : Nat) : Nat := 2 ^ Nat.log2 (n - 1)

theorem splitPoint_pos (n : Nat) : 0 < splitPoint n := Nat.two_pow_pos _

theorem splitPoint_lt {n : Nat} (h : 2 ≤ n) : splitPoint n < n := by
  have hne : n - 1 ≠ 0 := by omega
  have := Nat.log2_self_le hne
  simp only [splitPoint]
  omega

/-- RFC 9162's split leaves at most half the tree on the right: `n ≤ 2 * splitPoint n`. -/
theorem le_two_mul_splitPoint {n : Nat} (h : 2 ≤ n) : n ≤ 2 * splitPoint n := by
  have := Nat.lt_log2_self (n := n - 1)
  simp only [splitPoint, Nat.pow_succ] at *
  omega

theorem two_pow_eq_of_lt_two_mul {i j : Nat} (h1 : 2 ^ j < 2 * 2 ^ i) (h2 : 2 ^ i < 2 * 2 ^ j) :
    (2 : Nat) ^ i = 2 ^ j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · have hle : (2 : Nat) ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Nat.pow_succ] at hle
    omega
  · rw [h]
  · have hle : (2 : Nat) ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Nat.pow_succ] at hle
    omega

/-- The RFC 9162 decomposition of a tree of size `n` splits a prefix of size `m` at the same
point, whenever that prefix reaches past the split: this is why the `m > k` branch of the
consistency proof is well formed. -/
theorem splitPoint_eq_of_gt {m n : Nat} (h2 : 2 ≤ m) (hmn : m ≤ n) (hk : splitPoint n < m) :
    splitPoint m = splitPoint n := by
  have hn2 : 2 ≤ n := by omega
  have ham := Nat.log2_self_le (n := m - 1) (by omega)
  have hbn := Nat.log2_self_le (n := n - 1) (by omega)
  have ham' := Nat.lt_log2_self (n := m - 1)
  have hbn' := Nat.lt_log2_self (n := n - 1)
  simp only [splitPoint, Nat.pow_succ] at *
  exact two_pow_eq_of_lt_two_mul (by omega) (by omega)

/-! ## Hashing (I-D Section 2.7) -/

/-- Leaf hash `H(0x00 || leaf)` (I-D Section 2.7; `ahl-core` `leaf_hash`). -/
def leafHash (M : HashModel Key) (b : Bytes) : Digest := M.H (0x00 :: b)

/-- Internal node hash `H(0x01 || left || right)` (I-D Section 2.7;
`atl_core::core::merkle::hash_children`). -/
def nodeHash (M : HashModel Key) (l r : Digest) : Digest :=
  M.H (0x01 :: (l.octets ++ r.octets))

/-! ## The Merkle tree hash -/

/-- `MTH` over a list of leaf hashes, by the RFC 9162 Section 2.1 recursion
(`atl_core::core::merkle::compute_root`, which `ahl-core` delegates to).

The empty tree is the separate case the invariants page names: `MTH({}) = H()`. A single leaf
hash is its own root, because the leaf hashing has already been applied. -/
def MTHh (M : HashModel Key) : List Digest → Digest
  | [] => M.H []
  | [h] => h
  | a :: b :: rest =>
    nodeHash M
      (MTHh M ((a :: b :: rest).take (splitPoint (a :: b :: rest).length)))
      (MTHh M ((a :: b :: rest).drop (splitPoint (a :: b :: rest).length)))
termination_by hs => hs.length
decreasing_by
  · simp only [List.length_take]
    have := splitPoint_lt (n := (a :: b :: rest).length) (by simp)
    omega
  · have hpos := splitPoint_pos (a :: b :: rest).length
    have hlen : 0 < (a :: b :: rest).length := by simp
    simp only [List.length_drop]
    omega

/-- `MTH` over a list of entries: leaf-hash each, then take the tree hash (`ahl-core`
`tree_root`). -/
def MTH (M : HashModel Key) (L : List Bytes) : Digest := MTHh M (L.map (leafHash M))

@[simp] theorem MTHh_nil (M : HashModel Key) : MTHh M [] = M.H [] := by
  simp [MTHh]

@[simp] theorem MTHh_singleton (M : HashModel Key) (h : Digest) : MTHh M [h] = h := by
  simp [MTHh]

/-- The RFC 9162 recursion, for any list of two or more leaf hashes. -/
theorem MTHh_eq_node (M : HashModel Key) {hs : List Digest} (h : 2 ≤ hs.length) :
    MTHh M hs =
      nodeHash M (MTHh M (hs.take (splitPoint hs.length)))
        (MTHh M (hs.drop (splitPoint hs.length))) := by
  match hs, h with
  | _ :: _ :: _, _ => rw [MTHh]

/-! ## Inclusion proofs (RFC 9162 Section 2.1.3; I-D Section 7.5 step 3)

-- AMBIGUITY: RFC 9162 serializes an inclusion path bottom-up (the sibling nearest the leaf
-- first), and so does `atl_core`'s `InclusionProof`. The recursion below consumes it top-down,
-- because that is the direction the tree decomposition runs. `verifyInclusion` reverses the
-- path once at the entry point, so the exposed form is the RFC's; every lemma is stated about
-- `verifyInclusion`. -/

/-- Recompute a root from a leaf hash and a top-down sibling path (RFC 9162 Section 2.1.3.2).
`none` means the path is structurally unusable for the declared size. -/
def rootFromPath (M : HashModel Key) (leafH : Digest) (i n : Nat) (path : List Digest) :
    Option Digest :=
  if _h0 : n = 0 then none
  else if _h1 : n = 1 then (match path with | [] => some leafH | _ :: _ => none)
  else
    match path with
    | [] => none
    | p :: rest =>
      if i < splitPoint n then
        (rootFromPath M leafH i (splitPoint n) rest).map fun l => nodeHash M l p
      else
        (rootFromPath M leafH (i - splitPoint n) (n - splitPoint n) rest).map fun r =>
          nodeHash M p r
termination_by n
decreasing_by
  · exact splitPoint_lt (by omega)
  · have := splitPoint_pos n
    omega

/-- `Incl(leaf, i, n, root, π)` of the invariants page: the inclusion proof for entry `leaf` at
index `i` of a tree of size `n` opens `root` (`ahl-core` `verify_inclusion_proof`). The path is
in RFC order. -/
def verifyInclusion (M : HashModel Key) (leaf : Bytes) (i n : Nat) (root : Digest)
    (path : List Digest) : Prop :=
  rootFromPath M (leafHash M leaf) i n path.reverse = some root

/-! ## Consistency proofs (RFC 9162 Section 2.1.4)

-- AMBIGUITY: as for inclusion paths, RFC 9162 builds a consistency proof with the outermost
-- node LAST (`SUBPROOF(…) : MTH(…)` appends). The recursion below consumes it outermost-first;
-- `verifyConsistency` reverses once at the entry point. -/

/-- Recompute the pair `(old root, new root)` from a consistency proof, following the RFC 9162
Section 2.1.4 `SUBPROOF` structure. `oldRoot` is the root the verifier was handed, which the
RFC's `b = true` case uses as the seed. -/
def consistencyRoots (M : HashModel Key) (oldRoot : Digest) (m n : Nat) (b : Bool)
    (proof : List Digest) : Option (Digest × Digest) :=
  if _hmn : m = n then
    match b, proof with
    | true, [] => some (oldRoot, oldRoot)
    | false, [x] => some (x, x)
    | _, _ => none
  else if _hlt : m < n ∧ 0 < m then
    match proof with
    | [] => none
    | p :: rest =>
      if m ≤ splitPoint n then
        (consistencyRoots M oldRoot m (splitPoint n) b rest).map fun rs =>
          (rs.1, nodeHash M rs.2 p)
      else
        (consistencyRoots M oldRoot (m - splitPoint n) (n - splitPoint n) false rest).map
          fun rs => (nodeHash M p rs.1, nodeHash M p rs.2)
  else none
termination_by n
decreasing_by
  · exact splitPoint_lt (by omega)
  · have := splitPoint_pos n
    omega

/-- `Consistent(m, n, r_m, r_n, π)` of the invariants page: the RFC 9162 consistency proof
verifies (`ahl-core` `verify_consistency_proof`). The proof list is in RFC order. -/
def verifyConsistency (M : HashModel Key) (m n : Nat) (rm rn : Digest)
    (proof : List Digest) : Prop :=
  consistencyRoots M rm m n true proof.reverse = some (rm, rn)

/-! ## Authenticated range proofs (I-D Section 3.1 item 5, Section 7.4)

-- AMBIGUITY: RFC 9162 defines no range proof. The form below is the one `ahl-core`'s
-- `range_proof.rs` implements — the construction of the corpus adaptor profile
-- `ahl-test-log-v1` Section 8: the minimal set of subtree hashes covering everything OUTSIDE
-- the range, consumed positionally by the RFC 6962/9162 decomposition of `[0, tree_size)`. That
-- is the construction formalised here, not a hypothetical RFC one. -/

/-- Where a subtree `[offset, offset + size)` sits relative to the proven range `[from, to)`
(`range_proof.rs` `classify`). -/
inductive Span where
  /-- Entirely outside the range: one carried subtree hash covers it. -/
  | outside
  /-- Entirely inside the range: recomputed from the carried entries. -/
  | inside
  /-- Straddles a boundary: must be split further. -/
  | straddles

/-- `range_proof.rs` `classify`, on `Nat` (the crate saturates at `u64`; `Nat` cannot overflow,
so the saturation has no counterpart here). -/
def classify (offset size «from» to : Nat) : Span :=
  if offset + size ≤ «from» ∨ to ≤ offset then .outside
  else if «from» ≤ offset ∧ offset + size ≤ to then .inside
  else .straddles

/-- Recompute a subtree root from the carried entries and the proof's subtree hashes,
consuming the hash list left to right (`range_proof.rs` `recompute`; the crate threads a cursor
over one vector, this threads the remaining list). `entries` is the full carried entry list,
indexed from `from`. -/
def rangeRoot (M : HashModel Key) («from» to : Nat) (entries : List Bytes)
    (offset size : Nat) (nodes : List Digest) : Option (Digest × List Digest) :=
  match classify offset size «from» to with
  | .outside =>
    match nodes with
    | [] => none
    | p :: rest => some (p, rest)
  | .inside =>
    some (MTH M (((entries.drop (offset - «from»)).take size)), nodes)
  | .straddles =>
    if _h0 : size = 0 then none
    else if _h1 : size = 1 then none
    else
      match rangeRoot M «from» to entries offset (splitPoint size) nodes with
      | none => none
      | some (l, rest) =>
        match rangeRoot M «from» to entries (offset + splitPoint size) (size - splitPoint size)
            rest with
        | none => none
        | some (r, rest') => some (nodeHash M l r, rest')
termination_by size
decreasing_by
  · exact splitPoint_lt (by omega)
  · have := splitPoint_pos size
    omega

/-- `Range(from, to, n, root, E, π)` of the invariants page: the authenticated range proof
verifies (`ahl-core` `range_proof::verify`). Every carried subtree hash must be consumed, the
carried entry count must equal the range width, and the recomputation must open the
checkpoint root. -/
def verifyRange (M : HashModel Key) («from» to n : Nat) (root : Digest) (entries : List Bytes)
    (nodes : List Digest) : Prop :=
  «from» < to ∧ to ≤ n ∧ entries.length = to - «from» ∧
    rangeRoot M «from» to entries 0 n nodes = some (root, [])

end AhlProofs.Tree
