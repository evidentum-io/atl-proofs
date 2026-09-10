import AtlProofs.Inclusion
import AtlProofs.Consistency
import AtlProofs.Adversarial

/-!
# What is NOT proved

## This is a model

The theorems are properties of the **abstract functions** in `AtlProofs.Model`,
`AtlProofs.Inclusion` and `AtlProofs.Consistency`. There is no Charon/Aeneas
extraction, no translation, and no refinement argument connecting `atl-core`
to these definitions. Names were aligned (`verify_inclusion`,
`verify_consistency`, `hash_children`, `largest_power_of_2_less_than`,
`is_power_of_two`) so the two can be read side by side, which is a convenience
for the reader and not a proof.

The SHA-256 pin in `reports/PROOF.sha256` (against `atl-core` revision
`5229787cfcd5dcf76276435ae872feea3b6013e1`) is **drift detection**: CI fails if
those four files change. It is not a refinement proof.

## Iterative crate verifier vs recursive SUBPROOF

`verifyConsistency` models the **iterative** RFC 9162 §2.1.4.2 algorithm that
the crate ships. `subproof_consistency_sound` is soundness of the **recursive
SUBPROOF** reconstruction (`consistencyRoots`), ported from ahl-proofs Tree.

**One direction is now proved.** `iterFlags_alignOdd_eq_innerFlags` shows the
iterative loop, started from the `alignOdd (from_size - 1, to_size - 1)` state,
makes exactly the recursive recursion's left/right decisions;
`consistencyRoots_foldFlags` shows the iterative fold reconstructs exactly the
pair `consistencyRoots` builds from the reversed path. Together
(`verifyConsistency_isTrue_imp_subproof`) an `okTrue` from the iterative
verifier exhibits a verifying SUBPROOF over `path.reverse`, and
`consistency_sound` is soundness of the **iterative** verifier itself.

**The converse is not proved.** That every verifying SUBPROOF is accepted by
the iterative loop — completeness of the crate-shaped verifier — is not proved;
in particular nothing here shows the `maxConsistencyPathLen` and
`path.isEmpty` guards never reject an honest proof.

This is still soundness of a **model**. `consistency_sound` is a theorem about
`verifyConsistency` as defined in `AtlProofs.Consistency`, not about
`atl-core::verify_consistency`: there is no extraction and no refinement.

A guard-by-guard correspondence with `consistency.rs` (public guards, power-of-two
prepend of `old_root` which is not on the wire, `alignOdd` / `shiftWhileEven`
loops, per-hash left/right combine, final `fr`/`sr`/`sn` check) is recorded in
the module comment of `Consistency.lean`. No accepted-true mismatch was found.
The SHA-256 pin remains drift detection only.

## Inclusion leftover vs short path (`err` vs `Ok(false)`)

In `inclusion.rs`, an unused leftover hash after all splits is `Err`, while a
path that runs out mid-reconstruction is `Ok(false)`. `rootFromPath` returns
`none` for both, and `verifyInclusion` maps that `none` to `okFalse` except for
the explicit `n = 0`, `i ≥ n`, `n = 1` nonempty, and max-depth cases which are
`err`. Both `err` and `okFalse` are non-true; soundness is only about
`okTrue`.

## Not proved: SHA-256, Ed25519, leaf construction, Super-Tree

`H : Bytes → Digest` is a parameter. ATL leaf construction
`SHA256(0x00 || payload_hash || metadata_hash)` is outside the model.
`generate_inclusion_proof`, `generate_consistency_proof`, Super-Tree, and
`subtle::ct_eq` (modelled as `=`) are out of scope.

## Not proved: completeness

Only **soundness** of inclusion and consistency is proved: a proof that
verifies implies the property, or exhibits a collision. The converse — that the
honest prover can always produce a proof that verifies — is not proved, for
either verifier.

## Not proved: collision resistance

Conclusions are `… ∨ ∃ x y, Collision M.H x y`. That such a pair cannot feasibly
be produced is a statement about adversaries; it is not a Lean hypothesis.
`HashModel` assumes nothing about `H`.

## Not proved: overflow

The crate uses `u64` with `checked_*`. This model uses `Nat`. Saturation and
overflow are not modelled.

## Not proved: split-view, signatures, keys

Inclusion and consistency proofs say nothing about whether two parties were
shown the same log, nothing about checkpoint signatures, and nothing about
log-key compromise.

## A deliberate difference from ahl-proofs: `from_size == 0`

atl-core accepts `from_size == 0` with an empty path as `Ok(true)` (any tree is
consistent with the empty tree). ahl-proofs required `0 < m`. The iterative
function matches atl-core. The recursive SUBPROOF soundness theorem still
requires `0 < Lm.length`, like ahl-proofs.
-/
