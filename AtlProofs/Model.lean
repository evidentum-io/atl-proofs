/-!
# Abstract Merkle model for atl-core verifiers

This module fixes the model over which the atl-core Merkle **verifier** theorems
are stated. It deliberately knows nothing about SHA-256, Ed25519, Super-Tree,
ATL leaf construction, or `subtle::ConstantTimeEq`.

Two conventions carry the honesty requirement:

* Every cryptographic assumption is a **parameter** — a field of `HashModel` —
  never a global `axiom`. Nothing here is asserted about the real SHA-256.
* Collision resistance is **never** stated as injectivity of `H`. A fixed-width
  function over unbounded inputs is not injective, so the lemmas conclude
  `Collision` — an exhibited pair `a ≠ b` with `H a = H b`. That informal CR
  assumption is a statement about adversaries, not about functions.

Geometry (`splitPoint`, `MTHh`, `nodeHash`) is ported from
`evidentum-io/ahl-proofs` Tree (RFC 9162 Section 2.1), then specialized to
atl-core's verifier shape: inclusion is over an already-computed leaf hash,
and `H : Bytes → Digest` is a parameter.

Pinned against `atl-core` revision `5229787cfcd5dcf76276435ae872feea3b6013e1`
(`reports/ATL_CORE.rev`). The SHA-256 pin of the four Merkle files is drift
detection, not a refinement proof. There is no Charon/Aeneas extraction.
-/

namespace AtlProofs

/-- Octet strings. -/
abbrev Bytes := List UInt8

/-- A digest: exactly 32 octets, matching `atl_core::core::merkle::crypto::Hash`. -/
structure Digest where
  /-- The 32 raw digest octets. -/
  octets : Bytes
  /-- The width of a SHA-256 digest. -/
  length_eq : octets.length = 32

/-- Digests are determined by their octets: the length field is a proposition. -/
theorem Digest.eq_of_octets_eq {d e : Digest} (h : d.octets = e.octets) : d = e := by
  cases d
  cases e
  simp only at h
  subst h
  rfl

/-- Boolean equality of digests. Models `subtle::ConstantTimeEq` as `=`. -/
def Digest.beq (d e : Digest) : Bool := decide (d.octets = e.octets)

theorem Digest.beq_iff (d e : Digest) : d.beq e = true ↔ d = e := by
  simp [Digest.beq]
  constructor
  · exact Digest.eq_of_octets_eq
  · intro h
    cases h
    rfl

@[simp] theorem Digest.beq_self (d : Digest) : d.beq d = true :=
  (Digest.beq_iff d d).mpr rfl

/-- The 32-byte zero digest. Used as garbage in the simplified-impl attack. -/
def zeroDigest : Digest :=
  ⟨List.replicate 32 (0 : UInt8), by simp⟩

/-- An exhibited collision of `f`: a pair of distinct inputs with one output.

This is the *conclusion* of the soundness lemmas, never a hypothesis. -/
def Collision {α : Type} (f : Bytes → α) (a b : Bytes) : Prop :=
  a ≠ b ∧ f a = f b

/-- The hash primitive as a parameter. `H` stands for SHA-256 in atl-core;
nothing whatsoever is assumed of it. -/
structure HashModel where
  /-- The unkeyed digest function (SHA-256 in this revision). -/
  H : Bytes → Digest

/-- RFC 6962 node prefix `0x01` (`atl_core::core::merkle::crypto::NODE_PREFIX`). -/
def nodePrefix : UInt8 := 0x01

/-- Internal node hash `H(0x01 || left || right)` (`hash_children`). -/
def nodeHash (M : HashModel) (l r : Digest) : Digest :=
  M.H (nodePrefix :: (l.octets ++ r.octets))

/-! ## Two list facts, reproved

`List.take_add` and `List.drop_take` are in Lean's prelude, but both are proved
there with `Classical.choice` in their dependency footprint. Reproving them by
induction keeps the soundness theorems free of choice when the rest of the
argument is. -/

theorem take_add' {α : Type} : ∀ (i j : Nat) (l : List α),
    l.take (i + j) = l.take i ++ (l.drop i).take j
  | 0, _, _ => by simp
  | _ + 1, _, [] => by simp
  | i + 1, j, x :: xs => by
    rw [show i + 1 + j = (i + j) + 1 from by omega]
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append]
    rw [take_add' i j xs]

theorem drop_take' {α : Type} : ∀ (i j : Nat) (l : List α),
    (l.take j).drop i = (l.drop i).take (j - i)
  | 0, _, _ => by simp
  | _ + 1, _, [] => by simp
  | _ + 1, 0, _ :: _ => by simp
  | i + 1, j + 1, x :: xs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, Nat.succ_sub_succ]
    exact drop_take' i j xs

/-! ## The RFC 9162 split

`splitPoint` is `atl_core::core::merkle::helpers::largest_power_of_2_less_than`
on `Nat`. Crate `checked_*` / `u64` overflow is not modelled. -/

/-- The largest power of two strictly less than `n`, for `n ≥ 2`. -/
def splitPoint (n : Nat) : Nat := 2 ^ Nat.log2 (n - 1)

theorem splitPoint_pos (n : Nat) : 0 < splitPoint n := Nat.two_pow_pos _

theorem splitPoint_lt {n : Nat} (h : 2 ≤ n) : splitPoint n < n := by
  have hne : n - 1 ≠ 0 := by omega
  have := Nat.log2_self_le hne
  simp only [splitPoint]
  omega

/-- RFC 9162's split leaves at most half the tree on the right. -/
theorem le_two_mul_splitPoint {n : Nat} (h : 2 ≤ n) : n ≤ 2 * splitPoint n := by
  have := Nat.lt_log2_self (n := n - 1)
  simp only [splitPoint, Nat.pow_succ] at *
  omega

theorem two_pow_eq_of_lt_two_mul {i j : Nat} (h1 : 2 ^ j < 2 * 2 ^ i)
    (h2 : 2 ^ i < 2 * 2 ^ j) : (2 : Nat) ^ i = 2 ^ j := by
  rcases Nat.lt_trichotomy i j with h | h | h
  · have hle : (2 : Nat) ^ (i + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Nat.pow_succ] at hle
    omega
  · rw [h]
  · have hle : (2 : Nat) ^ (j + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [Nat.pow_succ] at hle
    omega

/-- The RFC 9162 decomposition of a tree of size `n` splits a prefix of size `m`
at the same point, whenever that prefix reaches past the split. -/
theorem splitPoint_eq_of_gt {m n : Nat} (h2 : 2 ≤ m) (hmn : m ≤ n) (hk : splitPoint n < m) :
    splitPoint m = splitPoint n := by
  have hn2 : 2 ≤ n := by omega
  have ham := Nat.log2_self_le (n := m - 1) (by omega)
  have hbn := Nat.log2_self_le (n := n - 1) (by omega)
  have ham' := Nat.lt_log2_self (n := m - 1)
  have hbn' := Nat.lt_log2_self (n := n - 1)
  simp only [splitPoint, Nat.pow_succ] at *
  exact two_pow_eq_of_lt_two_mul (by omega) (by omega)

/-! ## The Merkle tree hash -/

/-- `MTH` over a list of leaf hashes, by the RFC 9162 Section 2.1 recursion
(`atl_core::core::merkle::compute_root` / `compute_subtree_root`).

A single leaf hash is its own root: ATL leaf construction
`SHA256(0x00 || payload_hash || metadata_hash)` is **outside** this model.
`verify_inclusion` takes an already-computed leaf hash. -/
def MTHh (M : HashModel) : List Digest → Digest
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

@[simp] theorem MTHh_nil (M : HashModel) : MTHh M [] = M.H [] := by
  simp [MTHh]

@[simp] theorem MTHh_singleton (M : HashModel) (h : Digest) : MTHh M [h] = h := by
  simp [MTHh]

/-- The RFC 9162 recursion, for any list of two or more leaf hashes. -/
theorem MTHh_eq_node (M : HashModel) {hs : List Digest} (h : 2 ≤ hs.length) :
    MTHh M hs =
      nodeHash M (MTHh M (hs.take (splitPoint hs.length)))
        (MTHh M (hs.drop (splitPoint hs.length))) := by
  match hs, h with
  | _ :: _ :: _, _ => rw [MTHh]

/-! ## Collisions from equal node hashes -/

/-- Equal node hashes: equal children, or a collision. Both digests are exactly
32 octets, so the preimage splits uniquely. -/
theorem node_eq_or_collision (M : HashModel) {l r l' r' : Digest}
    (h : nodeHash M l r = nodeHash M l' r') :
    (l = l' ∧ r = r') ∨ ∃ x y, Collision M.H x y := by
  by_cases hpre : nodePrefix :: (l.octets ++ r.octets) =
      nodePrefix :: (l'.octets ++ r'.octets)
  · refine Or.inl ?_
    have happ : l.octets ++ r.octets = l'.octets ++ r'.octets := by simpa using hpre
    obtain ⟨hl, hr⟩ := List.append_inj happ (by rw [l.length_eq, l'.length_eq])
    exact ⟨Digest.eq_of_octets_eq hl, Digest.eq_of_octets_eq hr⟩
  · exact Or.inr ⟨_, _, hpre, h⟩

/-- Two leaf-hash lists of the same length with one tree hash are the same list,
or a collision has been exhibited. -/
theorem mthh_inj_aux (M : HashModel) :
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

/-- **The tree hash determines the leaf hashes.** Two leaf-hash lists of the same
length with the same tree hash are equal, or a collision of `H` has been
exhibited. -/
theorem mthh_inj_or_collision (M : HashModel) {hs hs' : List Digest}
    (hlen : hs.length = hs'.length) (h : MTHh M hs = MTHh M hs') :
    hs = hs' ∨ ∃ x y, Collision M.H x y :=
  mthh_inj_aux M hs.length hs hs' (Nat.le_refl _) hlen h

/-! ## Three-way verifier outcome

Mirrors `AtlResult<bool>`: `Err` / `Ok(false)` / `Ok(true)`. Equality of hashes
is modelled as `=`; the crate's `subtle::ConstantTimeEq` is not. -/

inductive VerifyResult where
  /-- `Err(_)`: structurally unusable input. -/
  | err
  /-- `Ok(false)`: well-formed but does not prove the claim. -/
  | okFalse
  /-- `Ok(true)`: the proof verifies. -/
  | okTrue
  deriving DecidableEq, Repr

/-- True exactly on `Ok(true)`. -/
def VerifyResult.isTrue : VerifyResult → Prop
  | .okTrue => True
  | .okFalse => False
  | .err => False

@[simp] theorem VerifyResult.isTrue_okTrue : VerifyResult.okTrue.isTrue := trivial

@[simp] theorem VerifyResult.isTrue_okFalse : VerifyResult.okFalse.isTrue = False := rfl

@[simp] theorem VerifyResult.isTrue_err : VerifyResult.err.isTrue = False := rfl

end AtlProofs
