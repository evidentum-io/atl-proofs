# atl-proofs

Machine-checked theorems about `atl-core`'s Merkle **verifiers**:

- `verify_inclusion` in `atl-core/src/core/merkle/inclusion.rs`
- `verify_consistency` in `atl-core/src/core/merkle/consistency.rs` (the
  iterative RFC 9162 §2.1.4.2 algorithm)

This is a **model**. There is no Charon/Aeneas extraction. The hash pin is
**drift detection**, not a refinement proof. Geometry lemmas (`splitPoint`,
`MTHh`, `nodeHash`, inclusion reconstruction, recursive SUBPROOF) are ported
from `evidentum-io/ahl-proofs` Tree (RFC 9162), then specialized to atl-core's
verifier shape.

No `sorry`. No `axiom` of our own: assumptions are parameters / structure
fields. Collision resistance is not a hypothesis; conclusions are
`P ∨ ∃ x y, Collision H x y`.

## Pins

| What | Value |
| --- | --- |
| Lean | `leanprover/lean4:v4.31.0` (`lean-toolchain`) |
| Mathlib / Lake deps | none |
| atl-core | `5229787cfcd5dcf76276435ae872feea3b6013e1` (`reports/ATL_CORE.rev`) |
| File hashes | `reports/PROOF.sha256` (paths relative to the atl-core root) |

CI clones `evidentum-io/atl-core` at that revision and runs
`sha256sum -c reports/PROOF.sha256` from the checkout.

## Reproduce

```sh
lake build
```

Toolchain: Lean 4.31.0, pinned in `lean-toolchain`. **No Mathlib**, and no
other dependency. The RFC 9162 split point needs `Nat.log2` and powers of two;
the prelude carries `Nat.log2_self_le`, `Nat.lt_log2_self`, `Nat.two_pow_pos`,
`Nat.pow_le_pow_right`.

## Proved

* **`inclusion_sound`.** If `verifyInclusion` returns `okTrue` against
  `MTHh M hs` at index `i`, then `hs[i]? = some leafH`, or a collision of `H`
  is exhibited. The verifier takes a leaf **hash** (atl-core's shape), not a
  raw entry. The index bound `i < n` is part of the verifier (RFC 9162
  §2.1.3.2).
* **`inclusion_rejects_index_42`.** Index 42 on a size-1 tree is rejected.
* **`simplified_impl_attack_rejected`.** The iterative crate-shaped verifier
  does **not** return true on the simplified-impl witness from
  `adversarial_tests.rs` (`from_size = 4`, `to_size = 8`,
  `path = [old_root, zeros, zeros]`), for every `HashModel` and every pair of
  roots. Rejection is structural (`sn == 0` mid-loop after prepend).
* **`zero_from_size_with_path_err`.** `from_size = 0` with a nonempty path is
  `err`.
* **`subproof_consistency_sound`.** Soundness of the **recursive SUBPROOF**
  reconstruction (`consistencyRoots`), ported from ahl-proofs: a verifying
  SUBPROOF from `(m, MTHh(L_m))` to `(n, MTHh(L_n))` shows `L_m` is the
  size-`m` prefix of `L_n`, or exhibits a collision.

`#print axioms` of the exported soundness/attack theorems is allowed to mention
only `propext`, `Classical.choice`, and `Quot.sound`.

## Not proved

* **The crate itself.** There is no extraction and no refinement. Do not claim
  `atl-core` is verified. The iterative function `verifyConsistency` is a
  model of `consistency.rs` by reading that file.
* **Iterative ↔ recursive equivalence.** `subproof_consistency_sound` is
  **not** soundness of the iterative algorithm the crate ships. That
  equivalence is not proved; see `AtlProofs/Boundary.lean`.
* **SHA-256, Ed25519, Super-Tree, proof generation.** `H` is a parameter.
  `generate_*` is out of scope.
* **ATL leaf construction** `SHA256(0x00 || payload_hash || metadata_hash)`.
  `verify_inclusion` takes an already-computed leaf hash; the model is `MTHh`
  over `List Digest`.
* **`subtle::ConstantTimeEq`.** Modelled as `=`.
* **Completeness** of the proof systems (honest prover always succeeds).
* **Collision resistance** as a hypothesis.
* **`u64` overflow / `checked_*`.** The model uses `Nat`.
* **Split-view, signatures, keys.**

## Model vs atl-core

| Crate | Lean |
| --- | --- |
| `Hash = [u8; 32]` | `Digest` |
| `hash_children` | `nodeHash` |
| `largest_power_of_2_less_than` | `splitPoint` |
| `is_power_of_two` | `isPowerOfTwo` |
| `compute_root` over leaf hashes | `MTHh` |
| `verify_inclusion` | `verifyInclusion` (`VerifyResult`) |
| `verify_consistency` (iterative) | `verifyConsistency` |
| `AtlResult<bool>` | `VerifyResult` (`err` / `okFalse` / `okTrue`) |
| `subtle::ct_eq` | `=` / `Digest.beq` |

`from_size == 0` with an empty path is `okTrue` (any tree consistent with
empty), matching atl-core; ahl-proofs required `0 < m`. The recursive SUBPROOF
soundness theorem still requires a nonempty old list.

Inclusion leftover hashes that `inclusion.rs` would `Err` may be `okFalse` in
the model when they also fail `rootFromPath`; both are non-true.

## Layout

```
AtlProofs/Model.lean         Bytes, Digest, Collision, HashModel, nodeHash, splitPoint, MTHh
AtlProofs/Inclusion.lean     verifyInclusion, inclusion_sound
AtlProofs/Consistency.lean   iterative verifier + recursive SUBPROOF soundness
AtlProofs/Adversarial.lean   simplified_impl_attack_rejected, inclusion_rejects_index_42
AtlProofs/Boundary.lean      what is not proved
```
