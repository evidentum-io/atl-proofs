import AtlProofs.Model
import AtlProofs.Inclusion
import AtlProofs.Consistency

/-!
# Adversarial witnesses

Theorems, not comments. The simplified-impl attack is rejected **structurally**
by the iterative RFC 9162 §2.1.4.2 loop: after prepending `old_root` (because
`from_size = 4` is a power of two), the path has four hashes and the loop hits
`sn == 0` before consuming the last element. No concrete SHA-256 or specific
leaves are required; the statement quantifies over every `HashModel`.
-/

namespace AtlProofs

/-- RFC 9162 §2.1.3.2 index bound: index 42 on a size-1 tree is rejected
however the recomputation would turn out. Mirrors the ahl-proofs example and
`inclusion.rs` (`leaf_index >= tree_size` → `Err`). -/
theorem inclusion_rejects_index_42 (M : HashModel) (leafH root : Digest) :
    ¬ (verifyInclusion M leafH 42 1 root []).isTrue := by
  unfold verifyInclusion
  have hn0 : ¬ (1 = 0) := by omega
  have hge : 42 ≥ 1 := by omega
  simp [hn0, hge]

/-- Public `from_size = 0` with a nonempty path is `err`
(`test_adversarial_zero_from_size_with_path`). -/
theorem zero_from_size_with_path_err (M : HashModel) (oldRoot newRoot : Digest)
    (a b : Digest) : verifyConsistency M 0 8 oldRoot newRoot [a, b] = .err :=
  consistency_zero_from_nonempty_err M 8 oldRoot newRoot a [b] (by omega)

/-- The iterative path check for the simplified-impl witness. After prepend,
`alignOdd (4-1) (8-1) = (0, 1)` and two remaining hashes after the first
subsequent element force `sn = 0`. -/
theorem simplified_impl_path_rejected (M : HashModel) (oldRoot newRoot : Digest)
    (p1 p2 : Digest) :
    verifyConsistencyPath M 4 8 [oldRoot, p1, p2] oldRoot newRoot = .okFalse := by
  have hp2 : isPowerOfTwo 4 = true := isPowerOfTwo_four
  have halign : alignOdd 3 7 = (0, 1) := alignOdd_three_seven
  simp [verifyConsistencyPath, hp2, halign, processConsist_fn0_sn1_two]

/-- Reduction of the public verifier on `(from, to) = (4, 8)` with a length-3
path to the inner iterative path check. -/
theorem verifyConsistency_four_eight_path (M : HashModel) (oldRoot newRoot : Digest)
    (p1 p2 : Digest) :
    verifyConsistency M 4 8 oldRoot newRoot [oldRoot, p1, p2] =
      verifyConsistencyPath M 4 8 [oldRoot, p1, p2] oldRoot newRoot := by
  unfold verifyConsistency
  rw [dif_neg (by decide : ¬ (4 > 8))]
  rw [dif_neg (by decide : ¬ (4 = 8))]
  rw [dif_neg (by decide : ¬ (4 = 0))]
  have hempty :
      ¬ (([oldRoot, p1, p2] : List Digest).isEmpty && !isPowerOfTwo 4) = true := by
    simp [isPowerOfTwo_four]
  rw [dif_neg hempty]
  have hlen : ¬ (([oldRoot, p1, p2] : List Digest).length > maxConsistencyPathLen 8) := by
    simp [maxConsistencyPathLen_eight]
  rw [dif_neg hlen]

/-- `test_regression_simplified_impl_vulnerability`:
`from_size = 4`, `to_size = 8`, `path = [old_root, zeros, zeros]` must not
return true. The simplified implementation accepted any power-of-two `from_size`
whose first hash equalled `old_root` and whose length was `O(log n)`. -/
theorem simplified_impl_attack_rejected (M : HashModel) (oldRoot newRoot : Digest) :
    ¬ (verifyConsistency M 4 8 oldRoot newRoot
        [oldRoot, zeroDigest, zeroDigest]).isTrue := by
  rw [verifyConsistency_four_eight_path, simplified_impl_path_rejected]
  simp

end AtlProofs
