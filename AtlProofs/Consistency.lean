import AtlProofs.Model

/-!
# Consistency verification

Two reconstructions live in this module and must not be confused:

1. **`verifyConsistency`** — the **iterative** RFC 9162 §2.1.4.2 algorithm that
   `atl-core` ships (`verify_consistency` + `verify_consistency_path` in
   `consistency.rs`). This is the function the crate runs and the function
   `adversarial_tests.rs` attacks. It is defined here so that attack and
   structural theorems are about the crate's shape.
2. **`consistencyRoots` / `verifyConsistencySubproof`** — the **recursive
   SUBPROOF** reconstruction, ported from `evidentum-io/ahl-proofs` Tree.
   `subproof_consistency_sound` is soundness of **that** reconstruction, not a
   refinement of the Rust. Iterative ↔ recursive equivalence is **not** proved.

`from_size == 0` with an empty path is `okTrue` (any tree is consistent with
the empty tree), matching atl-core and differing from ahl-proofs, which
required `0 < m`.
-/

namespace AtlProofs

/-! ## Power-of-two and bit length (helpers.rs / u64 bit ops on `Nat`) -/

/-- `n > 0 && (n & (n-1)) == 0`. Matches `is_power_of_two`; false for 0. -/
def isPowerOfTwo (n : Nat) : Bool := decide (0 < n ∧ n &&& (n - 1) = 0)

/-- Bit length of `n` as a `u64` would report it for values that fit:
`64 - n.leading_zeros()`, i.e. `0` when `n = 0` and `floor(log2 n) + 1`
otherwise. Crate `u64` overflow is not modelled. -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- `((64 - to_size.leading_zeros()) as usize).saturating_mul(2)` on `Nat`. -/
def maxConsistencyPathLen (toSize : Nat) : Nat := 2 * bitLength toSize

/-! ## Iterative RFC 9162 §2.1.4.2 (`verify_consistency_path`) -/

/-- Shift right while the LSB of `fn` is set (RFC step 4). -/
def alignOdd (fn sn : Nat) : Nat × Nat :=
  if h : fn % 2 = 1 then
    alignOdd (fn / 2) (sn / 2)
  else
    (fn, sn)
termination_by fn
decreasing_by
  apply Nat.div_lt_self
  · cases fn with
    | zero => simp at h
    | succ n => exact Nat.succ_pos n
  · omega

/-- Inner loop of RFC step 6b: shift while `fn` is even and nonzero. -/
def shiftWhileEven (fn sn : Nat) : Nat × Nat :=
  if h : fn ≠ 0 ∧ fn % 2 = 0 then
    shiftWhileEven (fn / 2) (sn / 2)
  else
    (fn, sn)
termination_by fn
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero h.1) (by omega)

/-- RFC steps 6–7: process each subsequent path element. -/
def processConsist (M : HashModel) (oldRoot newRoot : Digest)
    (fn sn : Nat) (fr sr : Digest) : List Digest → VerifyResult
  | [] =>
    if fr.beq oldRoot && sr.beq newRoot && sn == 0 then .okTrue else .okFalse
  | c :: rest =>
    if sn = 0 then .okFalse
    else
      let fr' := if fn % 2 = 1 ∨ fn = sn then nodeHash M c fr else fr
      let sr' := if fn % 2 = 1 ∨ fn = sn then nodeHash M c sr else nodeHash M sr c
      let fnMid := if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).1 else fn
      let snMid := if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).2 else sn
      processConsist M oldRoot newRoot (fnMid / 2) (snMid / 2) fr' sr' rest

/-- Private `verify_consistency_path`. Empty path is `okFalse` (trivials are
handled by the public function). If `from_size` is a power of two, `old_root`
is prepended. -/
def verifyConsistencyPath (M : HashModel) (fromSize toSize : Nat)
    (path : List Digest) (oldRoot newRoot : Digest) : VerifyResult :=
  match path with
  | [] => .okFalse
  | _ :: _ =>
    let pathVec := if isPowerOfTwo fromSize then oldRoot :: path else path
    let fn0 := fromSize - 1
    let sn0 := toSize - 1
    let (fn, sn) := alignOdd fn0 sn0
    match pathVec with
    | [] => .okFalse
    | h :: t => processConsist M oldRoot newRoot fn sn h h t

/-- Public `verify_consistency`. -/
def verifyConsistency (M : HashModel) (fromSize toSize : Nat)
    (oldRoot newRoot : Digest) (path : List Digest) : VerifyResult :=
  if _hgt : fromSize > toSize then .err
  else if _heq : fromSize = toSize then
    if path.isEmpty then
      if oldRoot.beq newRoot then .okTrue else .okFalse
    else .err
  else if _hz : fromSize = 0 then
    if path.isEmpty then .okTrue else .err
  else if _hemp : (path.isEmpty && !isPowerOfTwo fromSize) = true then .err
  else if _hlen : path.length > maxConsistencyPathLen toSize then .err
  else verifyConsistencyPath M fromSize toSize path oldRoot newRoot

/-! ## Structural lemmas about the iterative verifier -/

theorem processConsist_sn_zero_cons (M : HashModel) (oldRoot newRoot : Digest)
    (fn : Nat) (fr sr c : Digest) (rest : List Digest) :
    processConsist M oldRoot newRoot fn 0 fr sr (c :: rest) = .okFalse := by
  simp [processConsist]

theorem processConsist_fn0_sn1_two (M : HashModel) (oldRoot newRoot : Digest)
    (fr sr c d : Digest) (rest : List Digest) :
    processConsist M oldRoot newRoot 0 1 fr sr (c :: d :: rest) = .okFalse := by
  have hstep :
      processConsist M oldRoot newRoot 0 1 fr sr (c :: d :: rest) =
        processConsist M oldRoot newRoot 0 0 fr (nodeHash M sr c) (d :: rest) := by
    simp [processConsist]
  rw [hstep, processConsist_sn_zero_cons]

theorem alignOdd_of_odd (fn sn : Nat) (h : fn % 2 = 1) :
    alignOdd fn sn = alignOdd (fn / 2) (sn / 2) := by
  rw [alignOdd.eq_def, dif_pos h]

theorem alignOdd_of_even (fn sn : Nat) (h : ¬ (fn % 2 = 1)) :
    alignOdd fn sn = (fn, sn) := by
  rw [alignOdd.eq_def, dif_neg h]

theorem alignOdd_three_seven : alignOdd 3 7 = (0, 1) := by
  rw [alignOdd_of_odd 3 7 rfl]
  rw [alignOdd_of_odd 1 3 rfl]
  rw [alignOdd_of_even 0 1 (by decide)]

theorem isPowerOfTwo_four : isPowerOfTwo 4 = true := by
  simp [isPowerOfTwo]

theorem bitLength_eight : bitLength 8 = 4 := rfl

theorem maxConsistencyPathLen_eight : maxConsistencyPathLen 8 = 8 := by
  simp [maxConsistencyPathLen, bitLength_eight]

/-- Same-size consistency requires an empty path and equal roots. -/
theorem consistency_same_size (M : HashModel) (n : Nat) (oldRoot newRoot : Digest) :
    verifyConsistency M n n oldRoot newRoot [] =
      if oldRoot.beq newRoot then .okTrue else .okFalse := by
  unfold verifyConsistency
  rw [dif_neg (by omega : ¬ (n > n))]
  rw [dif_pos rfl]
  simp

/-- `from_size == 0` with an empty path is `okTrue` (any tree is consistent with
empty), matching atl-core. -/
theorem consistency_zero_from_empty (M : HashModel) (toSize : Nat)
    (oldRoot newRoot : Digest) (h : 0 < toSize) :
    verifyConsistency M 0 toSize oldRoot newRoot [] = .okTrue := by
  unfold verifyConsistency
  rw [dif_neg (by omega : ¬ (0 > toSize))]
  rw [dif_neg (by omega : ¬ (0 = toSize))]
  rw [dif_pos rfl]
  simp

/-- `from_size == 0` with a nonempty path is `err`
(`test_adversarial_zero_from_size_with_path`). -/
theorem consistency_zero_from_nonempty_err (M : HashModel) (toSize : Nat)
    (oldRoot newRoot p : Digest) (ps : List Digest) (h : 0 < toSize) :
    verifyConsistency M 0 toSize oldRoot newRoot (p :: ps) = .err := by
  unfold verifyConsistency
  rw [dif_neg (by omega : ¬ (0 > toSize))]
  rw [dif_neg (by omega : ¬ (0 = toSize))]
  rw [dif_pos rfl]
  simp

theorem consistency_from_gt_to_err (M : HashModel) (fromSize toSize : Nat)
    (oldRoot newRoot : Digest) (path : List Digest) (h : fromSize > toSize) :
    verifyConsistency M fromSize toSize oldRoot newRoot path = .err := by
  unfold verifyConsistency
  rw [dif_pos h]

/-! ## Recursive SUBPROOF reconstruction (ahl-proofs Tree)

Soundness below is of **this** reconstruction. It is not a claim that
`verifyConsistency` (the iterative crate model) is sound, and it is not a
refinement of `consistency.rs`. -/

/-- Recompute the pair `(old root, new root)` from a consistency proof, following
RFC 9162 §2.1.4 `SUBPROOF`. Consumes the path outermost-first. -/
def consistencyRoots (M : HashModel) (oldRoot : Digest) (m n : Nat) (b : Bool)
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

/-- `Consistent(m, n, r_m, r_n, π)` of the recursive SUBPROOF model. The proof
list is in RFC order (reversed once at the entry point). Requires `0 < m` in
the recursive case, unlike the iterative crate verifier which accepts
`from_size == 0`. -/
def verifyConsistencySubproof (M : HashModel) (m n : Nat) (rm rn : Digest)
    (proof : List Digest) : Prop :=
  consistencyRoots M rm m n true proof.reverse = some (rm, rn)

theorem consistencyRoots_self (M : HashModel) (s : Digest) (m : Nat) (b : Bool)
    (proof : List Digest) :
    consistencyRoots M s m m b proof =
      (match b, proof with
        | true, [] => some (s, s)
        | false, [x] => some (x, x)
        | _, _ => none) := by
  rw [consistencyRoots.eq_def, dif_pos rfl]

theorem consistencyRoots_step (M : HashModel) (s : Digest) {m n : Nat} (b : Bool)
    (hmn : m < n) (hm : 0 < m) (p : Digest) (rest : List Digest) :
    consistencyRoots M s m n b (p :: rest) =
      if m ≤ splitPoint n then
        (consistencyRoots M s m (splitPoint n) b rest).map fun rs => (rs.1, nodeHash M rs.2 p)
      else
        (consistencyRoots M s (m - splitPoint n) (n - splitPoint n) false rest).map fun rs =>
          (nodeHash M p rs.1, nodeHash M p rs.2) := by
  have h1 : ¬ (m = n) := by omega
  rw [consistencyRoots.eq_def, dif_neg h1, dif_pos (⟨hmn, hm⟩ : m < n ∧ 0 < m)]

theorem consistencyRoots_step_nil (M : HashModel) (s : Digest) {m n : Nat} (b : Bool)
    (hmn : m < n) (hm : 0 < m) : consistencyRoots M s m n b [] = none := by
  have h1 : ¬ (m = n) := by omega
  rw [consistencyRoots.eq_def, dif_neg h1, dif_pos (⟨hmn, hm⟩ : m < n ∧ 0 < m)]

theorem subproof_consistency_sound_aux (M : HashModel) :
    ∀ (N : Nat) (Lm Ln : List Digest) (m n : Nat) (b : Bool) (seed : Digest)
      (proof : List Digest),
      n ≤ N → Lm.length = m → Ln.length = n → 0 < m → m ≤ n →
      (b = true → seed = MTHh M Lm) →
      consistencyRoots M seed m n b proof = some (MTHh M Lm, MTHh M Ln) →
      Lm = Ln.take m ∨ ∃ x y, Collision M.H x y := by
  intro N
  induction N with
  | zero => intro _ _ m n _ _ _ hle _ _ hm hmn _ _; exact False.elim (by omega)
  | succ N ih =>
    intro Lm Ln m n b seed proof hle hlm hln hm hmn hb h
    by_cases heqmn : m = n
    · subst heqmn
      have hroots : MTHh M Lm = MTHh M Ln := by
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
      rcases mthh_inj_or_collision M (by omega) hroots with rfl | hc
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
        rw [MTHh_eq_node M (by omega : 2 ≤ Ln.length)] at h
        by_cases hmk : m ≤ splitPoint n
        · rw [if_pos hmk] at h
          obtain ⟨rs, hrs, heq⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨r1, r2⟩ := rs
          simp only [Prod.mk.injEq] at heq
          rcases node_eq_or_collision M heq.2 with ⟨hl, _⟩ | hc
          · have hlnk : (Ln.take (splitPoint n)).length = splitPoint n := by
              simp only [List.length_take]; omega
            have hrec : consistencyRoots M seed m (splitPoint n) b rest =
                some (MTHh M Lm, MTHh M (Ln.take (splitPoint Ln.length))) := by
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
          rw [MTHh_eq_node M (by omega : 2 ≤ Lm.length)] at h
          obtain ⟨rs, hrs, heq⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨r1, r2⟩ := rs
          simp only [Prod.mk.injEq] at heq
          rcases node_eq_or_collision M heq.1 with ⟨hpm, hrm⟩ | hc
          · rcases node_eq_or_collision M heq.2 with ⟨hpn, hrn⟩ | hc
            · have hprefix : MTHh M (Lm.take (splitPoint n)) = MTHh M (Ln.take (splitPoint n)) := by
                rw [hlm, hsp] at hpm
                rw [hln] at hpn
                rw [← hpm, ← hpn]
              have hlenm : (Lm.take (splitPoint n)).length = splitPoint n := by
                simp only [List.length_take]; omega
              have hlenn : (Ln.take (splitPoint n)).length = splitPoint n := by
                simp only [List.length_take]; omega
              rcases mthh_inj_or_collision M (by omega) hprefix with hheads | hc
              · have hlmd : (Lm.drop (splitPoint n)).length = m - splitPoint n := by
                  simp only [List.length_drop]; omega
                have hlnd : (Ln.drop (splitPoint n)).length = n - splitPoint n := by
                  simp only [List.length_drop]; omega
                have hrec : consistencyRoots M seed (m - splitPoint n) (n - splitPoint n) false
                    rest = some (MTHh M (Lm.drop (splitPoint n)), MTHh M (Ln.drop (splitPoint n))) := by
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

/-- **Soundness of the recursive SUBPROOF reconstruction**, not of the iterative
crate verifier. A verifying RFC 9162 SUBPROOF from `(m, MTHh(L_m))` to
`(n, MTHh(L_n))` shows that `L_m` is the size-`m` prefix of `L_n`, or exhibits
a collision of `H`. -/
theorem subproof_consistency_sound (M : HashModel) {Lm Ln : List Digest}
    {proof : List Digest} (hpos : 0 < Lm.length) (hmn : Lm.length ≤ Ln.length)
    (h : verifyConsistencySubproof M Lm.length Ln.length (MTHh M Lm) (MTHh M Ln) proof) :
    Lm = Ln.take Lm.length ∨ ∃ x y, Collision M.H x y :=
  subproof_consistency_sound_aux M Ln.length Lm Ln Lm.length Ln.length true (MTHh M Lm)
    proof.reverse (Nat.le_refl _) rfl rfl hpos hmn (fun _ => rfl) h

end AtlProofs
