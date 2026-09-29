-- Prove2me | Theorems.Thm_tropMatVecMul_shift_equivariant_nat
-- name    : tropMatVecMul_shift_equivariant_nat
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:10:16.734679+00:00
-- url     : https://prove2.me/theorems/93e1b6fc-e64f-4e2d-9dc9-adea181b2e57
-- title:
--   TropMatVecMul shift equivariant nat
-- statement:
--   Formal statement of `tropMatVecMul_shift_equivariant_nat` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem tropMatVecMul_shift_equivariant_nat    {m n : ℕ} (A : TropMat m n) (x : TropVec n) (c : ℕ) (i : Fin m) :
--       tropMatVecMul A (fun j => x j + (c : Trop)) i =
--       tropMatVecMul A x i + (c : Trop) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TropicalAlgebra/TropicalZKCommitments.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TropicalAlgebra/TropicalZKCommitments.lean#L180

-- Thm stub generated from Cryptography/TropicalAlgebra/TropicalZKCommitments.lean
import Mathlib
import Definitions.Def_Cryptography_TropicalAlgebra_TropicalZKCommitments
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Zero-Knowledge Commitments

This file develops a theory of commitment schemes and zero-knowledge protocols
over the tropical (min-plus) semiring, establishing both impossibility results
for naïve Pedersen-style approaches and constructive alternatives based on
tropical matrix actions.

## Main Results

### Part I: Impossibility (Theorem A)
* `IdempotentSemiring` — class for semirings with `a + a = a`
* `idempotent_semiring_trivial_inverses` — additive inverses force triviality
* `tropical_pedersen_impossible` — linear homomorphic commitments with hiding
  are impossible in idempotent semirings

### Part II: Tropical Matrix Commitments (Theorem B)
* `tropMatVecMul` — tropical matrix-vector product
* `tropCommit` — tropical matrix commitment `C(x, r) = A ⊗ x ⊓ B ⊗ r`
* `tropCommit_binding_of_injective` — binding from injectivity of `A`-action
* `tropMatVecMul_shift_equivariant` — shift equivariance of tropical product

### Part III: Zero-Knowledge by Shift Invariance (Theorem C)
* `TropTranscript` — Σ-protocol transcript type
* `transcript_shift` — global shift action on transcripts
* `transcript_shift_preserves_verification` — shifted transcripts remain valid
* `tropical_sigma_zk` — zero-knowledge: every valid transcript has a
  shifted equivalent that is simulatable

### Part IV: Idempotent Normalization and Composition (Theorem D)
* `normalizeVec` — idempotent normalization (componentwise `⊓`)
* `normalizeVec_idem` — normalization is idempotent
* `compose_transcripts` — sequential composition of transcripts
* `parallel_soundness_decay` — soundness error decays exponentially
  under parallel repetition

## References

* Butkovič, P. "Max-linear Systems: Theory and Algorithms" (2010)
* Grigoriev & Shpilrain "Tropical Cryptography" (2014)
-/

open Finset Function

set_option linter.unusedVariables false

/-! ## Part I: Impossibility of Pedersen-style Commitments in Idempotent Semirings -/








/-! ## Part II: Tropical Matrix Commitment and Binding -/







/-
**Theorem B: Binding from injectivity of the message encoding.**

    If the tropical matrix-vector product `A ⊗ (·)` is injective on the
    message space, and the commitment values determine the `A`-component
    (i.e. the `B ⊗ r` part doesn't obscure the `A ⊗ x` part), then
    collisions in commitments force message equality.

    This replaces group cancellation with order-theoretic rigidity:
    injectivity of `tropMatVecMul A` is a tropical analogue of
    "full column rank".
-/

/-
Tropical matrix-vector product is shift-equivariant:
    `A ⊗ (x + c) = (A ⊗ x) + c` where `+ c` means adding a constant
    to each component.

    This is the foundation for zero-knowledge: shifting the input
    shifts the output uniformly.
-/

theorem tropMatVecMul_shift_equivariant_nat    {m n : ℕ} (A : TropMat m n) (x : TropVec n) (c : ℕ) (i : Fin m) :
    tropMatVecMul A (fun j => x j + (c : Trop)) i =
    tropMatVecMul A x i + (c : Trop) := by sorry
