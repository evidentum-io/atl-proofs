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
   `subproof_consistency_sound` is soundness of **that** reconstruction.

The forward implication `okTrue` of the iterative verifier ⇒ recursive
SUBPROOF is proved (`verifyConsistency_isTrue_imp_subproof`). The converse
(every SUBPROOF is accepted by the iterative loop) is **not** proved.

`from_size == 0` with an empty path is `okTrue` (any tree is consistent with
the empty tree), matching atl-core and differing from ahl-proofs, which
required `0 < m`.

## Correspondence with `consistency.rs` (drift detection, not a refinement)

Public `verify_consistency` vs `verifyConsistency`, in order:

* `from_size > to_size` → `Err` / `.err`
* `from_size == to_size`: nonempty path → `Err` / `.err`; empty path →
  `Ok(ct_eq(old, new))` / `.okTrue`/`.okFalse` via `Digest.beq`
* `from_size == 0`: nonempty path → `Err` / `.err`; empty path → `Ok(true)` /
  `.okTrue`
* empty path and `from_size` not a power of two → `Err` / `.err`
* path longer than `2 * bitLength(to_size)` → `Err` / `.err`
* otherwise `verify_consistency_path`

Private `verify_consistency_path` vs `verifyConsistencyPath`:

* empty **wire** path → `Ok(false)` / `.okFalse` (before any prepend)
* if `from_size` is a power of two, **prepend** `old_root` (not on the wire)
* `fn = from_size - 1`, `sn = to_size - 1`
* shift both while LSB(`fn`) is set (`alignOdd`)
* `fr = sr = pathVec[0]`
* each subsequent hash: `sn == 0` → `Ok(false)`; if LSB(`fn`) set or `fn == sn`
  then hash the sibling on the **left** of both `fr`/`sr` and
  `shiftWhileEven`; else hash on the **right** of `sr` only; then shift both
  once
* final: `ct_eq(fr, old) && ct_eq(sr, new) && sn == 0`

No accepted-true mismatch was found against
`atl-core` `5229787cfcd5dcf76276435ae872feea3b6013e1`. Hash equality is
`=` rather than `subtle::ct_eq`; `Nat` rather than `u64`/`checked_*`.
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

/-- `alignOdd fn sn` strips trailing one-bits of `fn` (shift until even). -/
theorem alignOdd_spec (fn sn : Nat) :
    ∃ k, (alignOdd fn sn).1 = fn / 2 ^ k ∧
      (alignOdd fn sn).2 = sn / 2 ^ k ∧
      (alignOdd fn sn).1 % 2 = 0 ∧
      ∀ i < k, (fn / 2 ^ i) % 2 = 1 := by
  induction fn using Nat.strongRecOn generalizing sn with
  | ind fn ih =>
    by_cases h : fn % 2 = 1
    · have hpos : 0 < fn := by
        cases fn with
        | zero => simp at h
        | succ n => exact Nat.succ_pos n
      have hlt : fn / 2 < fn := Nat.div_lt_self hpos (by omega)
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (fn / 2) hlt (sn / 2)
      refine ⟨k + 1, ?_⟩
      rw [alignOdd_of_odd _ _ h]
      refine ⟨?_, ?_, hk3, ?_⟩
      · calc (alignOdd (fn / 2) (sn / 2)).1
            = fn / 2 / 2 ^ k := hk1
          _ = fn / 2 ^ (k + 1) := by
            rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
      · calc (alignOdd (fn / 2) (sn / 2)).2
            = sn / 2 / 2 ^ k := hk2
          _ = sn / 2 ^ (k + 1) := by
            rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
      · intro i hi
        cases i with
        | zero => simpa
        | succ i =>
          have hi' : i < k := by omega
          simpa [Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul] using hk4 i hi'
    · refine ⟨0, ?_⟩
      rw [alignOdd_of_even _ _ h]
      have he : fn % 2 = 0 := by omega
      simp [he]

theorem shiftWhileEven_of_zero (sn : Nat) : shiftWhileEven 0 sn = (0, sn) := by
  rw [shiftWhileEven.eq_def]
  simp

theorem shiftWhileEven_of_odd (fn sn : Nat) (h : fn % 2 = 1) :
    shiftWhileEven fn sn = (fn, sn) := by
  have : ¬ (fn ≠ 0 ∧ fn % 2 = 0) := by
    intro ⟨_, he⟩
    omega
  rw [shiftWhileEven.eq_def, dif_neg this]

theorem shiftWhileEven_of_even_pos (fn sn : Nat) (h0 : fn ≠ 0) (h2 : fn % 2 = 0) :
    shiftWhileEven fn sn = shiftWhileEven (fn / 2) (sn / 2) := by
  rw [shiftWhileEven.eq_def, dif_pos ⟨h0, h2⟩]

theorem shiftWhileEven_spec_pos (fn sn : Nat) (h0 : fn ≠ 0) :
    ∃ k, (shiftWhileEven fn sn).1 = fn / 2 ^ k ∧
      (shiftWhileEven fn sn).2 = sn / 2 ^ k ∧
      (shiftWhileEven fn sn).1 % 2 = 1 ∧
      ∀ i < k, (fn / 2 ^ i) % 2 = 0 := by
  induction fn using Nat.strongRecOn generalizing sn with
  | ind fn ih =>
    by_cases h2 : fn % 2 = 0
    · have hpos : 0 < fn := Nat.pos_of_ne_zero h0
      have hlt : fn / 2 < fn := Nat.div_lt_self hpos (by omega)
      have hnz : fn / 2 ≠ 0 := by
        intro hz
        omega
      rw [shiftWhileEven_of_even_pos _ _ h0 h2]
      obtain ⟨k, hk1, hk2, hk3, hk4⟩ := ih (fn / 2) hlt (sn / 2) hnz
      refine ⟨k + 1, ?_⟩
      refine ⟨?_, ?_, hk3, ?_⟩
      · calc (shiftWhileEven (fn / 2) (sn / 2)).1
            = fn / 2 / 2 ^ k := hk1
          _ = fn / 2 ^ (k + 1) := by
            rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
      · calc (shiftWhileEven (fn / 2) (sn / 2)).2
            = sn / 2 / 2 ^ k := hk2
          _ = sn / 2 ^ (k + 1) := by
            rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
      · intro i hi
        cases i with
        | zero => simp [h2]
        | succ i =>
          have hi' : i < k := by omega
          simpa [Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul] using hk4 i hi'
    · refine ⟨0, ?_⟩
      have hodd : fn % 2 = 1 := by omega
      rw [shiftWhileEven_of_odd _ _ hodd]
      simp [hodd]

/-- `shiftWhileEven fn sn` for `fn = 0` is `(0, sn)`; otherwise it divides out
trailing zeros of `fn` (stops at odd, so a power of two becomes `1` not `0`). -/
theorem shiftWhileEven_spec (fn sn : Nat) :
    if fn = 0 then
      shiftWhileEven fn sn = (0, sn)
    else
      ∃ k, (shiftWhileEven fn sn).1 = fn / 2 ^ k ∧
        (shiftWhileEven fn sn).2 = sn / 2 ^ k ∧
        (shiftWhileEven fn sn).1 % 2 = 1 ∧
        ∀ i < k, (fn / 2 ^ i) % 2 = 0 := by
  by_cases h0 : fn = 0
  · simp [h0, shiftWhileEven_of_zero]
  · simp only [h0, ↓reduceIte]
    exact shiftWhileEven_spec_pos fn sn h0

theorem shiftWhileEven_snd_le (fn sn : Nat) : (shiftWhileEven fn sn).2 ≤ sn := by
  have hspec := shiftWhileEven_spec fn sn
  by_cases h0 : fn = 0
  · simp [h0, shiftWhileEven_of_zero] at hspec ⊢
  · simp only [h0, ↓reduceIte] at hspec
    obtain ⟨k, _, hk2, _, _⟩ := hspec
    rw [hk2]
    exact Nat.div_le_self _ _

theorem shiftWhileEven_fst_le (fn sn : Nat) : (shiftWhileEven fn sn).1 ≤ fn := by
  have hspec := shiftWhileEven_spec fn sn
  by_cases h0 : fn = 0
  · simp [h0, shiftWhileEven_of_zero] at hspec ⊢
  · simp only [h0, ↓reduceIte] at hspec
    obtain ⟨k, hk1, _, _, _⟩ := hspec
    rw [hk1]
    exact Nat.div_le_self _ _

/-- One subsequent path element: exact `fr`/`sr` updates and `(fn, sn)`
transition. -/
theorem processConsist_step_spec (M : HashModel) (oldRoot newRoot : Digest)
    (fn sn : Nat) (fr sr c : Digest) (rest : List Digest) :
    processConsist M oldRoot newRoot fn sn fr sr (c :: rest) =
      if sn = 0 then .okFalse
      else
        let fr' := if fn % 2 = 1 ∨ fn = sn then nodeHash M c fr else fr
        let sr' := if fn % 2 = 1 ∨ fn = sn then nodeHash M c sr else nodeHash M sr c
        let fnMid := if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).1 else fn
        let snMid := if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).2 else sn
        processConsist M oldRoot newRoot (fnMid / 2) (snMid / 2) fr' sr' rest := by
  rfl

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

/-! ## Power-of-two facts and the iterative/recursive flag sequence -/

theorem two_pow_and_pred (k : Nat) : (2 ^ k) &&& (2 ^ k - 1) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hik : i < k
  · have : ¬ k = i := by omega
    simp [hik, this]
  · simp [hik]

theorem isPowerOfTwo_two_pow (k : Nat) : isPowerOfTwo (2 ^ k) = true := by
  simp only [isPowerOfTwo, decide_eq_true_eq]
  exact ⟨Nat.two_pow_pos k, two_pow_and_pred k⟩

theorem testBit_div_pow (n k : Nat) :
    n.testBit k = decide ((n / 2 ^ k) % 2 = 1) := by
  induction k generalizing n with
  | zero => simp [Nat.testBit_zero]
  | succ k ih =>
    rw [Nat.testBit_succ, Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    exact ih (n / 2)

theorem testBit_log2 (n : Nat) (hn : n ≠ 0) : n.testBit n.log2 = true := by
  have hle := Nat.log2_self_le hn
  have hlt := Nat.lt_log2_self (n := n)
  have hp : 0 < 2 ^ n.log2 := Nat.two_pow_pos _
  have hdiv : n / 2 ^ n.log2 = 1 := by
    have hge : 1 ≤ n / 2 ^ n.log2 := (Nat.le_div_iff_mul_le hp).mpr (by simpa using hle)
    have hlt' : n / 2 ^ n.log2 < 2 := (Nat.div_lt_iff_lt_mul hp).mpr (by
      simp only [Nat.pow_succ] at hlt
      simpa [Nat.mul_comm] using hlt)
    omega
  rw [testBit_div_pow, hdiv]
  simp

theorem testBit_odd_succ (n i : Nat) (h : n % 2 = 1) :
    (n - 1).testBit (i + 1) = n.testBit (i + 1) := by
  have hdiv : (n - 1) / 2 = n / 2 := by omega
  rw [Nat.testBit_succ, Nat.testBit_succ, hdiv]

theorem and_pred_div_two (n : Nat) (heven : n % 2 = 0) (hpos : 0 < n)
    (hand : n &&& (n - 1) = 0) : n / 2 &&& (n / 2 - 1) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h1 : (n / 2).testBit i = n.testBit (i + 1) := Nat.testBit_div_two _ _
  have h2 : (n / 2 - 1).testBit i = (n - 1).testBit (i + 1) := by
    have : (n - 1) / 2 = n / 2 - 1 := by omega
    rw [← Nat.testBit_div_two, this]
  rw [Nat.testBit_and, h1, h2, ← Nat.testBit_and, hand]
  simp [Nat.zero_testBit]

theorem isPowerOfTwo_eq_log2 (n : Nat) (h : isPowerOfTwo n = true) :
    n = 2 ^ n.log2 := by
  simp only [isPowerOfTwo, decide_eq_true_eq] at h
  revert h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro ⟨hpos, hand⟩
    by_cases h1 : n = 1
    · subst h1
      rfl
    · by_cases heven : n % 2 = 0
      · have hn2 : n / 2 < n := Nat.div_lt_self hpos (by omega)
        have hpos2 : 0 < n / 2 := by omega
        have hand2 := and_pred_div_two n heven hpos hand
        have heq := ih (n / 2) hn2 ⟨hpos2, hand2⟩
        have hmul : n = 2 * (n / 2) := by omega
        have hne : n / 2 ≠ 0 := by omega
        let L := (n / 2).log2
        have heqL : n / 2 = 2 ^ L := heq
        have hlog : n.log2 = L + 1 := by
          rw [Nat.log2_eq_iff (by omega)]
          constructor
          · have := Nat.log2_self_le hne
            change 2 ^ L ≤ n / 2 at this
            rw [Nat.pow_succ, Nat.mul_comm]
            omega
          · have := Nat.lt_log2_self (n := n / 2)
            change n / 2 < 2 ^ (L + 1) at this
            rw [Nat.pow_succ, Nat.mul_comm]
            omega
        have hpow : 2 * (n / 2) = 2 ^ n.log2 := by
          rw [heqL, hlog, Nat.pow_succ, Nat.mul_comm]
        exact hmul.trans hpow
      · have hodd : n % 2 = 1 := by omega
        have hnne : n ≠ 0 := by omega
        have hbit : n.testBit n.log2 = true := testBit_log2 n hnne
        have hpred : (n - 1).testBit n.log2 = true := by
          cases hL : n.log2 with
          | zero =>
            have hle := Nat.log2_self_le hnne
            have hlt := Nat.lt_log2_self (n := n)
            simp [hL] at hle hlt
            omega
          | succ L =>
            rw [hL] at hbit
            simpa [testBit_odd_succ n L hodd] using hbit
        have hnz : (n &&& (n - 1)).testBit n.log2 = true := by
          rw [Nat.testBit_and, hbit, hpred]
          rfl
        have : (n &&& (n - 1)).testBit n.log2 = false := by
          rw [hand, Nat.zero_testBit]
        simp [hnz] at this

theorem isPowerOfTwo_iff (n : Nat) : isPowerOfTwo n = true ↔ ∃ k, n = 2 ^ k := by
  constructor
  · intro h
    exact ⟨n.log2, isPowerOfTwo_eq_log2 n h⟩
  · intro ⟨k, hk⟩
    subst hk
    exact isPowerOfTwo_two_pow k

theorem isPowerOfTwo_le_splitPoint {m n : Nat} (hpot : isPowerOfTwo m = true)
    (hlt : m < n) : m ≤ splitPoint n := by
  have hm : m = 2 ^ m.log2 := isPowerOfTwo_eq_log2 m hpot
  have hmpos : 0 < m := by
    simp only [isPowerOfTwo, decide_eq_true_eq] at hpot
    exact hpot.1
  have hne : n - 1 ≠ 0 := by omega
  have hle : m ≤ n - 1 := by omega
  have hpow : 2 ^ m.log2 ≤ n - 1 := by rwa [← hm]
  have hk : m.log2 ≤ (n - 1).log2 := (Nat.le_log2 hne).mpr hpow
  simp only [splitPoint]
  rw [hm]
  exact Nat.pow_le_pow_right (by decide : (0 : Nat) < 2) hk

theorem div_splitPoint (n : Nat) (h : 2 ≤ n) : (n - 1) / splitPoint n = 1 := by
  have hne : n - 1 ≠ 0 := by omega
  have hle := Nat.log2_self_le hne
  have hlt := Nat.lt_log2_self (n := n - 1)
  simp only [splitPoint]
  have hp : 0 < 2 ^ (n - 1).log2 := Nat.two_pow_pos _
  have hge : 1 ≤ (n - 1) / 2 ^ (n - 1).log2 :=
    (Nat.le_div_iff_mul_le hp).mpr (by simpa using hle)
  have hlt' : (n - 1) / 2 ^ (n - 1).log2 < 2 :=
    (Nat.div_lt_iff_lt_mul hp).mpr (by
      simp only [Nat.pow_succ] at hlt
      simpa [Nat.mul_comm] using hlt)
  omega

theorem two_pow_pred_div (p t : Nat) (h : t ≤ p) :
    (2 ^ p - 1) / 2 ^ t = 2 ^ (p - t) - 1 := by
  have hp : 0 < 2 ^ t := Nat.two_pow_pos t
  have hpow : 2 ^ t * 2 ^ (p - t) = 2 ^ p := by
    rw [← Nat.pow_add, Nat.add_comm, Nat.sub_add_cancel h]
  have h1 : 1 ≤ 2 ^ (p - t) := Nat.one_le_pow (p - t) 2 (by omega)
  have hmul : 2 ^ t * (2 ^ (p - t) - 1) = 2 ^ p - 2 ^ t := by
    rw [Nat.mul_sub_left_distrib, hpow, Nat.mul_one]
  have hsum : 2 ^ t * (2 ^ (p - t) - 1) + (2 ^ t - 1) = 2 ^ p - 1 := by
    rw [hmul]
    have hle : 2 ^ t ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) h
    have hle2 : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
    omega
  have hdiv : (2 ^ t * (2 ^ (p - t) - 1) + (2 ^ t - 1)) / 2 ^ t =
      2 ^ (p - t) - 1 + (2 ^ t - 1) / 2 ^ t :=
    Nat.mul_add_div hp (2 ^ (p - t) - 1) (2 ^ t - 1)
  have hzero : (2 ^ t - 1) / 2 ^ t = 0 :=
    Nat.div_eq_of_lt (Nat.sub_lt (Nat.two_pow_pos t) (by omega))
  rw [← hsum, hdiv, hzero]
  simp

/-- Combine flags, inside-to-outside: `true` = left (hash sibling onto both),
`false` = right (hash sibling onto the new root only). -/
def innerFlags (m n : Nat) : List Bool :=
  if _h : m < n ∧ 0 < m then
    let k := splitPoint n
    if m ≤ k then innerFlags m k ++ [false]
    else innerFlags (m - k) (n - k) ++ [true]
  else []
termination_by n
decreasing_by
  · exact splitPoint_lt (by omega)
  · have := splitPoint_pos n
    omega

/-- Iterative L/R decisions from control state `(fn, sn)`, inside-to-outside. -/
def iterFlags (fn sn : Nat) : List Bool :=
  if h : sn = 0 then []
  else if hleft : fn % 2 = 1 ∨ fn = sn then
    true :: iterFlags ((shiftWhileEven fn sn).1 / 2) ((shiftWhileEven fn sn).2 / 2)
  else
    false :: iterFlags (fn / 2) (sn / 2)
termination_by sn
decreasing_by
  · have hpos : 0 < sn := Nat.pos_of_ne_zero h
    have hle := shiftWhileEven_snd_le fn sn
    have hlt := Nat.div_lt_self hpos (by omega : 1 < 2)
    have hle2 : (shiftWhileEven fn sn).2 / 2 ≤ sn / 2 := Nat.div_le_div_right hle
    exact Nat.lt_of_le_of_lt hle2 hlt
  · exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by omega : 1 < 2)

def foldFlags (M : HashModel) (fr sr : Digest) : List Digest → List Bool → Digest × Digest
  | c :: cs, f :: fs =>
    let fr' := if f then nodeHash M c fr else fr
    let sr' := if f then nodeHash M c sr else nodeHash M sr c
    foldFlags M fr' sr' cs fs
  | _, _ => (fr, sr)

theorem iterFlags_eq_nil (fn sn : Nat) : iterFlags fn sn = [] ↔ sn = 0 := by
  constructor
  · intro h
    by_cases hsn : sn = 0
    · exact hsn
    · rw [iterFlags.eq_def, dif_neg hsn] at h
      split at h <;> cases h
  · intro h
    subst h
    rw [iterFlags.eq_def]
    simp

theorem iterFlags_cons (fn sn : Nat) (h : sn ≠ 0) :
    iterFlags fn sn =
      decide (fn % 2 = 1 ∨ fn = sn) ::
        iterFlags
          ((if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).1 else fn) / 2)
          ((if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).2 else sn) / 2) := by
  rw [iterFlags.eq_def, dif_neg h]
  by_cases hleft : fn % 2 = 1 ∨ fn = sn
  · simp [hleft]
  · simp [hleft]

theorem innerFlags_of_ge (m n : Nat) (h : ¬ (m < n ∧ 0 < m)) : innerFlags m n = [] := by
  rw [innerFlags.eq_def, dif_neg h]

theorem innerFlags_of_lt (m n : Nat) (hm : 0 < m) (hlt : m < n) :
    innerFlags m n =
      if m ≤ splitPoint n then innerFlags m (splitPoint n) ++ [false]
      else innerFlags (m - splitPoint n) (n - splitPoint n) ++ [true] := by
  rw [innerFlags.eq_def, dif_pos ⟨hlt, hm⟩]

theorem foldFlags_nil_flags (M : HashModel) (fr sr : Digest) (cs : List Digest) :
    foldFlags M fr sr cs [] = (fr, sr) := by
  cases cs <;> rfl

theorem foldFlags_nil_cs (M : HashModel) (fr sr : Digest) (fs : List Bool) :
    foldFlags M fr sr [] fs = (fr, sr) := by
  cases fs <;> rfl

theorem foldFlags_cons (M : HashModel) (fr sr c : Digest) (cs : List Digest)
    (f : Bool) (fs : List Bool) :
    foldFlags M fr sr (c :: cs) (f :: fs) =
      foldFlags M (if f then nodeHash M c fr else fr)
        (if f then nodeHash M c sr else nodeHash M sr c) cs fs := rfl

theorem processConsist_nil (M : HashModel) (oldRoot newRoot : Digest)
    (fn sn : Nat) (fr sr : Digest) :
    processConsist M oldRoot newRoot fn sn fr sr [] =
      if fr.beq oldRoot && sr.beq newRoot && sn == 0 then .okTrue else .okFalse :=
  rfl

theorem snMid_lt (fn sn : Nat) (hsn : sn ≠ 0) :
    (if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).2 else sn) / 2 < sn := by
  have hpos : 0 < sn := Nat.pos_of_ne_zero hsn
  have hle : (if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).2 else sn) ≤ sn :=
    if hleft : fn % 2 = 1 ∨ fn = sn then by
      simp [hleft]
      exact shiftWhileEven_snd_le fn sn
    else by
      simp [hleft]
  have hlt : sn / 2 < sn := Nat.div_lt_self hpos (by omega)
  have : (if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).2 else sn) / 2 ≤ sn / 2 :=
    Nat.div_le_div_right hle
  omega

theorem processConsist_iterFlags (M : HashModel) (oldRoot newRoot : Digest)
    (fn sn : Nat) (fr sr : Digest) (cs : List Digest)
    (hlen : cs.length = (iterFlags fn sn).length) :
    processConsist M oldRoot newRoot fn sn fr sr cs =
      let rs := foldFlags M fr sr cs (iterFlags fn sn)
      if rs.1.beq oldRoot && rs.2.beq newRoot then .okTrue else .okFalse := by
  induction sn using Nat.strongRecOn generalizing fn fr sr cs with
  | ind sn ih =>
    by_cases hsn : sn = 0
    · subst hsn
      have hf : iterFlags fn 0 = [] := (iterFlags_eq_nil fn 0).mpr rfl
      have hcs : cs = [] := List.length_eq_zero_iff.mp (by simpa [hf] using hlen)
      subst hcs
      simp [processConsist_nil, foldFlags_nil_cs, hf]
    · rw [iterFlags_cons fn sn hsn] at hlen ⊢
      match cs with
      | [] => simp at hlen
      | c :: rest =>
        rw [processConsist_step_spec]
        simp only [hsn, ↓reduceIte]
        have hlen' : rest.length =
            (iterFlags
              ((if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).1 else fn) / 2)
              ((if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).2 else sn) / 2)).length := by
          simpa using hlen
        have hdec := snMid_lt fn sn hsn
        have ih' := ih
          ((if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).2 else sn) / 2) hdec
          ((if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).1 else fn) / 2)
          (if fn % 2 = 1 ∨ fn = sn then nodeHash M c fr else fr)
          (if fn % 2 = 1 ∨ fn = sn then nodeHash M c sr else nodeHash M sr c)
          rest hlen'
        rw [foldFlags_cons]
        by_cases hleft : fn % 2 = 1 ∨ fn = sn
        · simp only [hleft, ↓reduceIte, decide_true] at ih' ⊢
          exact ih'
        · simp only [hleft, ↓reduceIte, decide_false] at ih' ⊢
          exact ih'

theorem processConsist_isTrue_of_length (M : HashModel) (oldRoot newRoot : Digest)
    (fn sn : Nat) (fr sr : Digest) (cs : List Digest)
    (hlen : cs.length = (iterFlags fn sn).length)
    (h : (processConsist M oldRoot newRoot fn sn fr sr cs).isTrue) :
    (foldFlags M fr sr cs (iterFlags fn sn)).1 = oldRoot ∧
      (foldFlags M fr sr cs (iterFlags fn sn)).2 = newRoot := by
  have heq := processConsist_iterFlags M oldRoot newRoot fn sn fr sr cs hlen
  rw [heq] at h
  cases hbeq : (foldFlags M fr sr cs (iterFlags fn sn)).1.beq oldRoot &&
      (foldFlags M fr sr cs (iterFlags fn sn)).2.beq newRoot
  · simp [hbeq] at h
  · simp [hbeq] at h
    have hf := (Bool.and_eq_true _ _).mp hbeq
    exact ⟨(Digest.beq_iff _ _).mp hf.1, (Digest.beq_iff _ _).mp hf.2⟩

theorem processConsist_length_of_isTrue (M : HashModel) (oldRoot newRoot : Digest)
    (fn sn : Nat) (fr sr : Digest) (cs : List Digest)
    (h : (processConsist M oldRoot newRoot fn sn fr sr cs).isTrue) :
    cs.length = (iterFlags fn sn).length := by
  induction sn using Nat.strongRecOn generalizing fn fr sr cs with
  | ind sn ih =>
    by_cases hsn : sn = 0
    · subst hsn
      cases cs with
      | nil =>
        have hf : iterFlags fn 0 = [] := (iterFlags_eq_nil fn 0).mpr rfl
        simp [hf]
      | cons _ _ =>
        rw [processConsist_sn_zero_cons] at h
        exact False.elim h
    · cases cs with
      | nil =>
        rw [processConsist_nil] at h
        simp [hsn] at h
      | cons c rest =>
        rw [processConsist_step_spec] at h
        simp only [hsn, ↓reduceIte] at h
        have hdec := snMid_lt fn sn hsn
        have ih' := ih
          ((if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).2 else sn) / 2) hdec
          ((if fn % 2 = 1 ∨ fn = sn then (shiftWhileEven fn sn).1 else fn) / 2)
          (if fn % 2 = 1 ∨ fn = sn then nodeHash M c fr else fr)
          (if fn % 2 = 1 ∨ fn = sn then nodeHash M c sr else nodeHash M sr c)
          rest h
        rw [iterFlags_cons fn sn hsn]
        simpa using ih'

/-! Flag correspondence: `iterFlags` after `alignOdd` equals recursive `innerFlags`. -/

theorem alignOdd_trailing_unique (fn k1 k2 : Nat)
    (he1 : (fn / 2 ^ k1) % 2 = 0) (ht1 : ∀ i < k1, (fn / 2 ^ i) % 2 = 1)
    (he2 : (fn / 2 ^ k2) % 2 = 0) (ht2 : ∀ i < k2, (fn / 2 ^ i) % 2 = 1) :
    k1 = k2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := ht2 k1 h; omega
  · exact h
  · have := ht1 k2 h; omega

theorem alignOdd_same_shift (fn sn1 sn2 : Nat) :
    ∃ k, (alignOdd fn sn1).1 = fn / 2 ^ k ∧ (alignOdd fn sn1).2 = sn1 / 2 ^ k ∧
      (alignOdd fn sn2).1 = fn / 2 ^ k ∧ (alignOdd fn sn2).2 = sn2 / 2 ^ k ∧
      (fn / 2 ^ k) % 2 = 0 ∧ ∀ i < k, (fn / 2 ^ i) % 2 = 1 := by
  obtain ⟨k1, h11, h12, he1, ht1⟩ := alignOdd_spec fn sn1
  obtain ⟨k2, h21, h22, he2, ht2⟩ := alignOdd_spec fn sn2
  have he1' : (fn / 2 ^ k1) % 2 = 0 := by rw [← h11]; exact he1
  have he2' : (fn / 2 ^ k2) % 2 = 0 := by rw [← h21]; exact he2
  have hk : k1 = k2 := alignOdd_trailing_unique fn k1 k2 he1' ht1 he2' ht2
  subst hk
  exact ⟨k1, h11, h12, h21, h22, he1', ht1⟩

theorem iterFlags_zero_sn (fn : Nat) : iterFlags fn 0 = [] :=
  (iterFlags_eq_nil fn 0).mpr rfl

theorem iterFlags_zero_one : iterFlags 0 1 = [false] := by
  rw [iterFlags_cons 0 1 (by omega)]
  have : ¬ (0 % 2 = 1 ∨ 0 = 1) := by omega
  simp [iterFlags_zero_sn]

/-- When `sn = 2^b - 1` the machine only `/2`s, for `b` steps. -/
theorem iterFlags_all_ones (fn b : Nat) (hfn : fn < 2 ^ b) :
    (iterFlags fn (2 ^ b - 1)).length = b := by
  induction b generalizing fn with
  | zero => simp [iterFlags_zero_sn]
  | succ b ih =>
    have hsn : 2 ^ (b + 1) - 1 ≠ 0 := by
      have h2 : 2 ≤ 2 ^ (b + 1) := by
        have : (2 : Nat) = 2 ^ 1 := rfl
        rw [this]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by omega : 1 < 2) h2))
    rw [iterFlags_cons fn (2 ^ (b + 1) - 1) hsn]
    have hdiv : (2 ^ (b + 1) - 1) / 2 = 2 ^ b - 1 :=
      two_pow_pred_div (b + 1) 1 (by omega)
    have hsnodd : (2 ^ (b + 1) - 1) % 2 = 1 := by
      have : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
      omega
    by_cases hod : fn % 2 = 1
    · have : fn % 2 = 1 ∨ fn = 2 ^ (b + 1) - 1 := Or.inl hod
      simp [this, shiftWhileEven_of_odd fn (2 ^ (b + 1) - 1) hod, hdiv]
      refine ih (fn / 2) ?_
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
        have : 2 * 2 ^ b = 2 ^ (b + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        omega)
    · have hne : ¬ fn = 2 ^ (b + 1) - 1 := by
        intro heq
        rw [heq] at hod
        exact hod hsnodd
      have : ¬ (fn % 2 = 1 ∨ fn = 2 ^ (b + 1) - 1) := by
        intro h; rcases h with h | h
        · exact hod h
        · exact hne h
      simp [this, hdiv]
      refine ih (fn / 2) ?_
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
        have : 2 * 2 ^ b = 2 ^ (b + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
        omega)

theorem iterFlags_div_hi (fn sn b : Nat) (hfn : fn < 2 ^ b)
    (hlo : 2 ^ b ≤ sn) (hhi : sn < 2 ^ (b + 1)) :
    iterFlags fn sn = iterFlags fn (2 ^ b - 1) ++ [false] := by
  induction b generalizing fn sn with
  | zero =>
    have hfn0 : fn = 0 := by omega
    have hsn1 : sn = 1 := by omega
    subst hfn0
    subst hsn1
    simp [iterFlags_zero_sn, iterFlags_zero_one]
  | succ b ih =>
    have hsn : sn ≠ 0 :=
      Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos (b + 1)) hlo)
    have hones : 2 ^ (b + 1) - 1 ≠ 0 := by
      have h2 : 2 ≤ 2 ^ (b + 1) := by
        have : (2 : Nat) = 2 ^ 1 := rfl
        rw [this]
        exact Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.ne_of_gt (Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le (by omega : 1 < 2) h2))
    rw [iterFlags_cons fn sn hsn, iterFlags_cons fn (2 ^ (b + 1) - 1) hones]
    have hne : ¬ fn = sn := Nat.ne_of_lt (Nat.lt_of_lt_of_le hfn hlo)
    have hdiv_ones : (2 ^ (b + 1) - 1) / 2 = 2 ^ b - 1 :=
      two_pow_pred_div (b + 1) 1 (by omega)
    by_cases hod : fn % 2 = 1
    · have hl : fn % 2 = 1 ∨ fn = sn := Or.inl hod
      have hl' : fn % 2 = 1 ∨ fn = 2 ^ (b + 1) - 1 := Or.inl hod
      simp [hl, hl', shiftWhileEven_of_odd fn sn hod,
        shiftWhileEven_of_odd fn (2 ^ (b + 1) - 1) hod, hdiv_ones]
      refine ih (fn / 2) (sn / 2) (by omega) ?_ ?_
      · exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr (by
          simpa [Nat.mul_comm, Nat.pow_succ] using hlo)
      · exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
          simpa [Nat.mul_comm, Nat.pow_succ] using hhi)
    · have hl : ¬ (fn % 2 = 1 ∨ fn = sn) := by
        intro h; rcases h with h | h
        · exact hod h
        · exact hne h
      have hl' : ¬ (fn % 2 = 1 ∨ fn = 2 ^ (b + 1) - 1) := by
        intro h; rcases h with h | h
        · exact hod h
        · have hodd : (2 ^ (b + 1) - 1) % 2 = 1 := by
            have : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
            omega
          rw [h] at hod
          exact hod hodd
      simp [hl, hl', hdiv_ones]
      refine ih (fn / 2) (sn / 2) (by omega) ?_ ?_
      · exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr (by
          simpa [Nat.mul_comm, Nat.pow_succ] using hlo)
      · exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
          simpa [Nat.mul_comm, Nat.pow_succ] using hhi)

theorem shiftWhileEven_two_pow (q : Nat) :
    shiftWhileEven (2 ^ q) (2 ^ q) = (1, 1) := by
  induction q with
  | zero =>
    rw [shiftWhileEven_of_odd 1 1 (by omega)]
  | succ q ih =>
    have h0 : 2 ^ (q + 1) ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos _)
    have h2 : 2 ^ (q + 1) % 2 = 0 := by
      rw [Nat.pow_succ, Nat.mul_comm]
      omega
    rw [shiftWhileEven_of_even_pos _ _ h0 h2]
    have hdiv : 2 ^ (q + 1) / 2 = 2 ^ q := by
      rw [Nat.pow_succ, Nat.mul_comm]
      omega
    rw [hdiv, ih]

theorem iterFlags_self_pow (q : Nat) : iterFlags (2 ^ q) (2 ^ q) = [true] := by
  have hsn : 2 ^ q ≠ 0 := Nat.ne_of_gt (Nat.two_pow_pos q)
  rw [iterFlags.eq_def, dif_neg hsn]
  rw [dif_pos (Or.inr rfl), shiftWhileEven_two_pow]
  simp [iterFlags_zero_sn]

theorem add_pow_div_two (fn q : Nat) (hq : 0 < q) :
    (fn + 2 ^ q) / 2 = fn / 2 + 2 ^ (q - 1) := by
  have hpow : 2 ^ q = 2 * 2 ^ (q - 1) := by
    cases q with
    | zero => omega
    | succ q => simp [Nat.pow_succ, Nat.mul_comm]
  omega

theorem two_pow_even (q : Nat) (hq : 0 < q) : 2 ^ q % 2 = 0 := by
  cases q with
  | zero => omega
  | succ q =>
    rw [Nat.pow_succ, Nat.mul_comm]
    omega

theorem shiftWhileEven_same_add (fn q : Nat) (hlt : fn < 2 ^ q) :
    ∃ r, (shiftWhileEven fn fn).1 < 2 ^ r ∧
      shiftWhileEven (fn + 2 ^ q) (fn + 2 ^ q) =
        ((shiftWhileEven fn fn).1 + 2 ^ r, (shiftWhileEven fn fn).2 + 2 ^ r) := by
  induction fn using Nat.strongRecOn generalizing q with
  | ind fn ih =>
    by_cases h0 : fn = 0
    · subst h0
      refine ⟨0, ?_, ?_⟩
      · simp [shiftWhileEven_of_zero]
      · simp [shiftWhileEven_of_zero, shiftWhileEven_two_pow]
    · by_cases hod : fn % 2 = 1
      · have hq : 0 < q := by
          cases q with
          | zero => omega
          | succ _ => omega
        refine ⟨q, ?_, ?_⟩
        · rw [shiftWhileEven_of_odd fn fn hod]
          exact hlt
        · rw [shiftWhileEven_of_odd fn fn hod]
          have hodd' : (fn + 2 ^ q) % 2 = 1 := by
            have := two_pow_even q hq
            omega
          rw [shiftWhileEven_of_odd (fn + 2 ^ q) (fn + 2 ^ q) hodd']
      · have hq0 : 0 < q := by
          cases q with
          | zero => omega
          | succ _ => omega
        have h2 : fn % 2 = 0 := by omega
        have hlt' : fn / 2 < 2 ^ (q - 1) :=
          (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
            have : 2 ^ (q - 1) * 2 = 2 ^ q := by
              cases q with
              | zero => omega
              | succ q => simp [Nat.pow_succ, Nat.mul_comm]
            omega)
        rw [shiftWhileEven_of_even_pos fn fn h0 h2]
        have h0' : fn + 2 ^ q ≠ 0 := by omega
        have h2' : (fn + 2 ^ q) % 2 = 0 := by
          have := two_pow_even q hq0
          omega
        rw [shiftWhileEven_of_even_pos (fn + 2 ^ q) (fn + 2 ^ q) h0' h2',
          add_pow_div_two fn q hq0]
        exact ih (fn / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by omega))
          (q - 1) hlt'

theorem pow_mul_two (q : Nat) (hq : 0 < q) : 2 ^ (q - 1) * 2 = 2 ^ q := by
  cases q with
  | zero => omega
  | succ q => simp [Nat.pow_succ, Nat.mul_comm]

theorem iterFlags_high_both (fn sn q : Nat)
    (hfnle : fn ≤ sn) (hfn : fn < 2 ^ q) (hsn : sn < 2 ^ q) :
    iterFlags (fn + 2 ^ q) (sn + 2 ^ q) = iterFlags fn sn ++ [true] := by
  induction sn using Nat.strongRecOn generalizing fn q with
  | ind sn ih =>
    by_cases hsz : sn = 0
    · subst hsz
      have : fn = 0 := by omega
      subst this
      simp [iterFlags_zero_sn, iterFlags_self_pow]
    · have hq : 0 < q := by
        cases q with
        | zero => omega
        | succ _ => omega
      have hsnq : sn + 2 ^ q ≠ 0 :=
        Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos q) (Nat.le_add_left _ _))
      rw [iterFlags.eq_def (fn := fn + 2 ^ q) (sn := sn + 2 ^ q), dif_neg hsnq]
      rw [iterFlags.eq_def (fn := fn) (sn := sn), dif_neg hsz]
      have hiff : (fn + 2 ^ q) % 2 = 1 ∨ fn + 2 ^ q = sn + 2 ^ q ↔
          fn % 2 = 1 ∨ fn = sn := by
        have hev := two_pow_even q hq
        constructor <;> intro h <;> rcases h with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      by_cases hleft : fn % 2 = 1 ∨ fn = sn
      · rw [dif_pos (hiff.mpr hleft), dif_pos hleft]
        simp only [List.cons_append]
        congr 1
        by_cases hod : fn % 2 = 1
        · rw [shiftWhileEven_of_odd fn sn hod,
            shiftWhileEven_of_odd (fn + 2 ^ q) (sn + 2 ^ q) (by
              have := two_pow_even q hq; omega)]
          rw [add_pow_div_two fn q hq, add_pow_div_two sn q hq]
          refine ih (sn / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega))
            (fn / 2) (q - 1) (Nat.div_le_div_right hfnle) ?_ ?_
          · exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
              rw [pow_mul_two q hq]; omega)
          · exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
              rw [pow_mul_two q hq]; omega)
        · have heq : fn = sn := by
            rcases hleft with h | h
            · exact False.elim (hod h)
            · exact h
          subst heq
          obtain ⟨r, hrlt, hr⟩ := shiftWhileEven_same_add fn q hfn
          rw [hr]
          have hsame : (shiftWhileEven fn fn).1 = (shiftWhileEven fn fn).2 := by
            obtain ⟨k, h1, h2, _, _⟩ := shiftWhileEven_spec_pos fn fn (by omega)
            rw [h1, h2]
          rw [← hsame]
          have hr0 : 0 < r := by
            cases r with
            | zero =>
              have hne : fn ≠ 0 := by omega
              obtain ⟨k, h1, _, h3, _⟩ := shiftWhileEven_spec_pos fn fn hne
              have : 0 < (shiftWhileEven fn fn).1 := by
                have : (shiftWhileEven fn fn).1 % 2 = 1 := h3
                omega
              simp at hrlt
              omega
            | succ _ => omega
          rw [add_pow_div_two ((shiftWhileEven fn fn).1) r hr0]
          refine ih ((shiftWhileEven fn fn).1 / 2)
            (Nat.lt_of_le_of_lt (Nat.div_le_div_right (shiftWhileEven_fst_le fn fn))
              (Nat.div_lt_self (by omega : 0 < fn) (by omega : 1 < 2)))
            ((shiftWhileEven fn fn).1 / 2) (r - 1) (Nat.le_refl _) ?_ ?_
          · exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
              rw [pow_mul_two r hr0]; omega)
          · exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
              rw [pow_mul_two r hr0]; omega)
      · rw [dif_neg (by
            intro h
            exact hleft (hiff.mp h)), dif_neg hleft]
        simp only [List.cons_append]
        congr 1
        rw [add_pow_div_two fn q hq, add_pow_div_two sn q hq]
        refine ih (sn / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hsz) (by omega))
          (fn / 2) (q - 1) (Nat.div_le_div_right hfnle) ?_ ?_
        · exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
            rw [pow_mul_two q hq]; omega)
        · exact (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr (by
            rw [pow_mul_two q hq]; omega)

theorem div_add_two_pow (a p t : Nat) (h : t ≤ p) :
    (2 ^ p + a) / 2 ^ t = 2 ^ (p - t) + a / 2 ^ t := by
  have hp := Nat.two_pow_pos t
  have : 2 ^ p = 2 ^ t * 2 ^ (p - t) := by
    rw [← Nat.pow_add, Nat.add_comm, Nat.sub_add_cancel h]
  rw [this, Nat.mul_add_div hp]

/-! ## Bridge: the iterative flag sequence is the recursive one

`iterFlags` is read off the crate's control state `(fn, sn)`; `innerFlags` is
read off the recursive `SUBPROOF` recursion. The theorem below shows the two
lists coincide once `alignOdd` has done the crate's initial right-shift, which
is what makes `subproof_consistency_sound` a statement about the shipped
iterative loop. -/

/-- `2 ^ p / 2 ^ t = 2 ^ (p - t)` for `t ≤ p`. -/
theorem two_pow_div_two_pow (p t : Nat) (h : t ≤ p) : (2 : Nat) ^ p / 2 ^ t = 2 ^ (p - t) := by
  have hsplit : (2 : Nat) ^ p = 2 ^ t * 2 ^ (p - t) := by
    rw [← Nat.pow_add, Nat.add_comm, Nat.sub_add_cancel h]
  rw [hsplit, Nat.mul_div_cancel_left _ (Nat.two_pow_pos t)]

/-- A value below `2 ^ b` whose first `b` bits are all set is `2 ^ b - 1`. -/
theorem all_ones_of_lt : ∀ (b x : Nat), x < 2 ^ b → (∀ i < b, (x / 2 ^ i) % 2 = 1) →
    x = 2 ^ b - 1 := by
  intro b
  induction b with
  | zero =>
    intro x hx _
    have : (2 : Nat) ^ 0 = 1 := rfl
    omega
  | succ b ih =>
    intro x hx ht
    have h0 : x % 2 = 1 := by simpa using ht 0 (by omega)
    have hstep : (2 : Nat) ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
    have hxd : x / 2 < 2 ^ b := by omega
    have hd : ∀ i < b, (x / 2 / 2 ^ i) % 2 = 1 := by
      intro i hi
      have hti := ht (i + 1) (by omega)
      rwa [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul] at hti
    have hrec := ih (x / 2) hxd hd
    have hp : 0 < 2 ^ b := Nat.two_pow_pos b
    omega

/-- `alignOdd` is pinned by any witness of the trailing-ones count of `fn`. -/
theorem alignOdd_eq_of_spec (fn sn j : Nat) (he : (fn / 2 ^ j) % 2 = 0)
    (ht : ∀ i < j, (fn / 2 ^ i) % 2 = 1) :
    alignOdd fn sn = (fn / 2 ^ j, sn / 2 ^ j) := by
  obtain ⟨k, hk1, hk2, hk3, hk4⟩ := alignOdd_spec fn sn
  have hk3' : (fn / 2 ^ k) % 2 = 0 := by rw [← hk1]; exact hk3
  have hkj : k = j := alignOdd_trailing_unique fn k j hk3' hk4 he ht
  subst hkj
  rw [← hk1, ← hk2]

/-- **Flag-sequence bridge (Step A).** Started from the control state
`alignOdd (from_size - 1, to_size - 1)` that `verify_consistency_path`
computes, the iterative loop makes exactly the left/right decisions of the
recursive `SUBPROOF` recursion. -/
theorem iterFlags_alignOdd_eq_innerFlags :
    ∀ (n m : Nat), 0 < m → m < n →
      iterFlags (alignOdd (m - 1) (n - 1)).1 (alignOdd (m - 1) (n - 1)).2 = innerFlags m n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro m hm hmn
    have hn2 : 2 ≤ n := by omega
    have hklt : splitPoint n < n := splitPoint_lt hn2
    have hkle2 : n ≤ 2 * splitPoint n := le_two_mul_splitPoint hn2
    have hkpos : 0 < splitPoint n := splitPoint_pos n
    obtain ⟨b, hkeq⟩ : ∃ b, splitPoint n = 2 ^ b := ⟨Nat.log2 (n - 1), rfl⟩
    have hpow2 : (2 : Nat) ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
    have hb1 : 2 ^ b ≤ n - 1 := by omega
    have hb2 : n - 1 < 2 ^ (b + 1) := by omega
    rw [innerFlags_of_lt m n hm hmn]
    by_cases hmk : m ≤ splitPoint n
    · rw [if_pos hmk]
      obtain ⟨j, hj1, hj2, hje0, hjt⟩ := alignOdd_spec (m - 1) (n - 1)
      have hje : ((m - 1) / 2 ^ j) % 2 = 0 := by rw [← hj1]; exact hje0
      have hm1 : m - 1 < 2 ^ b := by omega
      have hjb : j ≤ b := by
        rcases Nat.lt_or_ge b j with hcon | hcon
        · have hbj := hjt b hcon
          rw [Nat.div_eq_of_lt hm1] at hbj
          omega
        · exact hcon
      have hkdiv : (splitPoint n - 1) / 2 ^ j = 2 ^ (b - j) - 1 := by
        rw [hkeq]
        exact two_pow_pred_div b j hjb
      have hmdiv_lt : (m - 1) / 2 ^ j < 2 ^ (b - j) := by
        have h1 : (m - 1) / 2 ^ j ≤ (2 ^ b - 1) / 2 ^ j := Nat.div_le_div_right (by omega)
        rw [two_pow_pred_div b j hjb] at h1
        have h2 : 0 < 2 ^ (b - j) := Nat.two_pow_pos _
        omega
      have hnlo : 2 ^ (b - j) ≤ (n - 1) / 2 ^ j := by
        have h1 : (2 : Nat) ^ b / 2 ^ j ≤ (n - 1) / 2 ^ j := Nat.div_le_div_right hb1
        rwa [two_pow_div_two_pow b j hjb] at h1
      have hnhi : (n - 1) / 2 ^ j < 2 ^ ((b - j) + 1) := by
        have h1 : (n - 1) / 2 ^ j ≤ (2 ^ (b + 1) - 1) / 2 ^ j :=
          Nat.div_le_div_right (by omega)
        rw [two_pow_pred_div (b + 1) j (by omega), show b + 1 - j = (b - j) + 1 from by omega]
          at h1
        have h2 : 0 < 2 ^ ((b - j) + 1) := Nat.two_pow_pos _
        omega
      rw [hj1, hj2, iterFlags_div_hi _ _ (b - j) hmdiv_lt hnlo hnhi]
      have halignk : alignOdd (m - 1) (splitPoint n - 1) =
          ((m - 1) / 2 ^ j, (splitPoint n - 1) / 2 ^ j) :=
        alignOdd_eq_of_spec (m - 1) (splitPoint n - 1) j hje hjt
      congr 1
      rcases Nat.lt_or_ge m (splitPoint n) with hlt | hge
      · have hih := ih (splitPoint n) hklt m hm hlt
        have hk1 : (alignOdd (m - 1) (splitPoint n - 1)).1 = (m - 1) / 2 ^ j := by rw [halignk]
        have hk2 : (alignOdd (m - 1) (splitPoint n - 1)).2 = (splitPoint n - 1) / 2 ^ j := by
          rw [halignk]
        rw [hk1, hk2] at hih
        rwa [hkdiv] at hih
      · have hmeq : m = splitPoint n := by omega
        have hmk1 : m - 1 = 2 ^ b - 1 := by omega
        have hdiv : (m - 1) / 2 ^ j = 2 ^ (b - j) - 1 := by
          rw [hmk1]; exact two_pow_pred_div b j hjb
        have hbj : b = j := by
          rcases Nat.lt_or_ge j b with hcon | hcon
          · exfalso
            have hpos : 0 < b - j := by omega
            have heven := two_pow_even (b - j) hpos
            have hone : 1 ≤ 2 ^ (b - j) := Nat.one_le_pow _ _ (by omega)
            rw [hdiv] at hje
            omega
          · omega
        have hz : (2 : Nat) ^ (b - j) - 1 = 0 := by
          simp [show b - j = 0 from by omega]
        rw [hz, iterFlags_zero_sn, innerFlags_of_ge m (splitPoint n) (by omega)]
    · rw [if_neg hmk]
      have hkm : splitPoint n < m := by omega
      have hxlt : m - splitPoint n - 1 < 2 ^ b := by omega
      have hylt : n - splitPoint n - 1 < 2 ^ b := by omega
      obtain ⟨j, hj1, hj2, hje0, hjt⟩ :=
        alignOdd_spec (m - splitPoint n - 1) (n - splitPoint n - 1)
      have hje : ((m - splitPoint n - 1) / 2 ^ j) % 2 = 0 := by rw [← hj1]; exact hje0
      have hjb : j ≤ b := by
        rcases Nat.lt_or_ge b j with hcon | hcon
        · have hbj := hjt b hcon
          rw [Nat.div_eq_of_lt hxlt] at hbj
          omega
        · exact hcon
      have hjltb : j < b := by
        rcases Nat.lt_or_ge j b with h | h
        · exact h
        · exfalso
          have hall : ∀ i < b, ((m - splitPoint n - 1) / 2 ^ i) % 2 = 1 := fun i hi =>
            hjt i (by omega)
          have hx := all_ones_of_lt b (m - splitPoint n - 1) hxlt hall
          omega
      have hm1 : m - 1 = 2 ^ b + (m - splitPoint n - 1) := by omega
      have hn1 : n - 1 = 2 ^ b + (n - splitPoint n - 1) := by omega
      have hdivm : ∀ i, i ≤ b → (m - 1) / 2 ^ i =
          2 ^ (b - i) + (m - splitPoint n - 1) / 2 ^ i := by
        intro i hi
        rw [hm1]
        exact div_add_two_pow _ b i hi
      have hdivn : ∀ i, i ≤ b → (n - 1) / 2 ^ i =
          2 ^ (b - i) + (n - splitPoint n - 1) / 2 ^ i := by
        intro i hi
        rw [hn1]
        exact div_add_two_pow _ b i hi
      have hmje : ((m - 1) / 2 ^ j) % 2 = 0 := by
        rw [hdivm j hjb]
        have hev := two_pow_even (b - j) (by omega)
        omega
      have hmjt : ∀ i < j, ((m - 1) / 2 ^ i) % 2 = 1 := by
        intro i hi
        rw [hdivm i (by omega)]
        have h1 := two_pow_even (b - i) (by omega)
        have h2 := hjt i hi
        omega
      have halign : alignOdd (m - 1) (n - 1) = ((m - 1) / 2 ^ j, (n - 1) / 2 ^ j) :=
        alignOdd_eq_of_spec (m - 1) (n - 1) j hmje hmjt
      have ha1 : (alignOdd (m - 1) (n - 1)).1 = (m - 1) / 2 ^ j := by rw [halign]
      have ha2 : (alignOdd (m - 1) (n - 1)).2 = (n - 1) / 2 ^ j := by rw [halign]
      have hxq : (m - splitPoint n - 1) / 2 ^ j < 2 ^ (b - j) := by
        have h1 : (m - splitPoint n - 1) / 2 ^ j ≤ (2 ^ b - 1) / 2 ^ j :=
          Nat.div_le_div_right (by omega)
        rw [two_pow_pred_div b j hjb] at h1
        have h2 : 0 < 2 ^ (b - j) := Nat.two_pow_pos _
        omega
      have hyq : (n - splitPoint n - 1) / 2 ^ j < 2 ^ (b - j) := by
        have h1 : (n - splitPoint n - 1) / 2 ^ j ≤ (2 ^ b - 1) / 2 ^ j :=
          Nat.div_le_div_right (by omega)
        rw [two_pow_pred_div b j hjb] at h1
        have h2 : 0 < 2 ^ (b - j) := Nat.two_pow_pos _
        omega
      have hxyq : (m - splitPoint n - 1) / 2 ^ j ≤ (n - splitPoint n - 1) / 2 ^ j :=
        Nat.div_le_div_right (by omega)
      rw [ha1, ha2, hdivm j hjb, hdivn j hjb,
        Nat.add_comm (2 ^ (b - j)) ((m - splitPoint n - 1) / 2 ^ j),
        Nat.add_comm (2 ^ (b - j)) ((n - splitPoint n - 1) / 2 ^ j),
        iterFlags_high_both _ _ (b - j) hxyq hxq hyq]
      congr 1
      have hih := ih (n - splitPoint n) (by omega) (m - splitPoint n) (by omega) (by omega)
      rwa [hj1, hj2] at hih

end AtlProofs
