import AtlProofs.Model

/-!
# Inclusion verification (`atl-core` `verify_inclusion`)

Port of `rootFromPath` / inclusion soundness from `evidentum-io/ahl-proofs` Tree,
specialized to atl-core's shape: the verifier takes an already-computed **leaf
hash**, not a raw entry. ATL leaf construction is outside the model.

`verifyInclusion` is a three-way function matching `inclusion.rs`:
* `tree_size == 0` → `err`
* `leaf_index >= tree_size` → `err`
* `tree_size == 1` → empty path required, then `leaf_hash == expected_root`
* path longer than `ceil(log2(n))` → `err`
* reconstruct root with RFC 6962 split (`splitPoint`)
* leftover unused / unusable path → not `okTrue`
* success iff reconstructed root equals expected

The index bound is part of the verifier (RFC 9162 §2.1.3.2).

Path order: RFC 9162 serializes inclusion paths bottom-up (sibling nearest the
leaf first), and so does `atl-core`'s `InclusionProof`. `rootFromPath` consumes
the path top-down; `verifyInclusion` reverses once at the entry point.
-/

namespace AtlProofs

/-- `ceil(log2 n)` for `n > 1`, matching `(64 - (tree_size - 1).leading_zeros())`
as a `u64` bit-length for values that fit. Overflow of crate `u64` is not
modelled. -/
def maxInclusionDepth (n : Nat) : Nat := Nat.log2 (n - 1) + 1

/-- Recompute a root from a leaf hash and a top-down sibling path
(RFC 9162 §2.1.3.2). `none` means the path is structurally unusable for the
declared size. -/
def rootFromPath (M : HashModel) (leafH : Digest) (i n : Nat) (path : List Digest) :
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

/-- Crate-shaped inclusion verifier (`verify_inclusion`). The path is in RFC
(leaf-to-root) order. -/
def verifyInclusion (M : HashModel) (leafH : Digest) (i n : Nat) (root : Digest)
    (path : List Digest) : VerifyResult :=
  if _h0 : n = 0 then .err
  else if _hge : i ≥ n then .err
  else if _h1 : n = 1 then
    match path with
    | [] => if leafH.beq root then .okTrue else .okFalse
    | _ :: _ => .err
  else if _hlen : path.length > maxInclusionDepth n then .err
  else
    match rootFromPath M leafH i n path.reverse with
    | none => .okFalse
    | some r => if r.beq root then .okTrue else .okFalse

theorem rootFromPath_one (M : HashModel) (leafH : Digest) (i : Nat) :
    rootFromPath M leafH i 1 [] = some leafH := by
  rw [rootFromPath]; simp

theorem rootFromPath_one_cons (M : HashModel) (leafH p : Digest) (i : Nat)
    (rest : List Digest) : rootFromPath M leafH i 1 (p :: rest) = none := by
  rw [rootFromPath]; simp

theorem rootFromPath_nil (M : HashModel) (leafH : Digest) {i n : Nat} (h : 2 ≤ n) :
    rootFromPath M leafH i n [] = none := by
  rw [rootFromPath]
  have h0 : ¬ (n = 0) := by omega
  have h1 : ¬ (n = 1) := by omega
  simp [h0, h1]

theorem rootFromPath_cons (M : HashModel) (leafH : Digest) {i n : Nat} (h : 2 ≤ n)
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

/-- `Ok(true)` implies the index bound and a successful RFC reconstruction. -/
theorem verifyInclusion_isTrue_imp (M : HashModel) (leafH : Digest) (i n : Nat)
    (root : Digest) (path : List Digest)
    (h : (verifyInclusion M leafH i n root path).isTrue) :
    i < n ∧ rootFromPath M leafH i n path.reverse = some root := by
  unfold verifyInclusion at h
  by_cases hn0 : n = 0
  · rw [dif_pos hn0] at h
    exact False.elim h
  rw [dif_neg hn0] at h
  by_cases hge : i ≥ n
  · rw [dif_pos hge] at h
    exact False.elim h
  rw [dif_neg hge] at h
  have hi : i < n := Nat.not_le.mp hge
  by_cases hn1 : n = 1
  · rw [dif_pos hn1] at h
    cases path with
    | nil =>
      cases hbeq : leafH.beq root
      · simp [hbeq] at h
      · simp [hbeq] at h
        have heq : leafH = root := (Digest.beq_iff leafH root).mp hbeq
        refine ⟨hi, ?_⟩
        subst hn1
        simp [rootFromPath_one, heq]
    | cons _ _ =>
      simp at h
  rw [dif_neg hn1] at h
  by_cases hlen : path.length > maxInclusionDepth n
  · rw [dif_pos hlen] at h
    exact False.elim h
  rw [dif_neg hlen] at h
  cases hroot : rootFromPath M leafH i n path.reverse with
  | none => simp [hroot] at h
  | some r =>
    simp [hroot] at h
    cases hbeq : r.beq root
    · simp [hbeq] at h
    · simp [hbeq] at h
      have heq : r = root := (Digest.beq_iff r root).mp hbeq
      exact ⟨hi, congrArg some heq⟩

theorem inclusion_sound_aux (M : HashModel) :
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

/-- **Inclusion soundness.** A verifying inclusion proof for leaf hash `leafH`
at index `i` against `MTHh M hs` shows that `hs[i]? = some leafH` — or exhibits
a collision of `H`. -/
theorem inclusion_sound (M : HashModel) {hs : List Digest} {leafH : Digest} {i : Nat}
    {path : List Digest} (h : (verifyInclusion M leafH i hs.length (MTHh M hs) path).isTrue) :
    hs[i]? = some leafH ∨ ∃ x y, Collision M.H x y := by
  obtain ⟨hi, hroot⟩ := verifyInclusion_isTrue_imp M leafH i hs.length (MTHh M hs) path h
  exact inclusion_sound_aux M hs.length hs leafH i path.reverse (Nat.le_refl _) hi hroot

/-- A one-leaf tree: the empty path opens the root. -/
theorem inclusion_singleton_empty_path (M : HashModel) (h : Digest) :
    (verifyInclusion M h 0 1 (MTHh M [h]) []).isTrue := by
  unfold verifyInclusion
  simp [Digest.beq_self]

/-- A two-leaf tree: the sibling leaf hash opens the root for the left leaf. -/
theorem inclusion_two_left (M : HashModel) (a b : Digest) :
    (verifyInclusion M a 0 2 (MTHh M [a, b]) [b]).isTrue := by
  have hsplit : splitPoint 2 = 1 := rfl
  have hpath : rootFromPath M a 0 2 [b] = some (nodeHash M a b) := by
    rw [rootFromPath_cons M a (by omega) b [], hsplit, if_pos (by omega),
      rootFromPath_one]
    simp
  have hroot : MTHh M [a, b] = nodeHash M a b := by
    rw [MTHh_eq_node M (by simp)]
    simp [hsplit]
  have hlen : ¬ ([b].length > maxInclusionDepth 2) := by simp [maxInclusionDepth]
  unfold verifyInclusion
  rw [dif_neg (by omega : ¬ (2 = 0))]
  rw [dif_neg (by omega : ¬ (0 ≥ 2))]
  rw [dif_neg (by omega : ¬ (2 = 1))]
  rw [dif_neg hlen]
  simp [hpath, hroot]

end AtlProofs
