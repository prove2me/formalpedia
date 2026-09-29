-- Prove2me | Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
-- name    : mme_kronPow_fiber_grouping_preserves_tensor_and_basis
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T11:56:34.712558+00:00
-- url     : https://prove2.me/theorems/561dd423-e71b-4af9-bf4c-83c9e187b5f7
-- title:
--   Tensor powers regroup by arbitrary finite fibers with exact word-basis action
-- statement:
--   Let T be a finite-dimensional tensor with chosen bases in its modes. Any bijection between N elementary positions and the disjoint union of groups of sizes n_j gives a tensor-preserving family of linear equivalences from T to the Nth Kronecker power to the product of the powers T^{n_j}. On each word basis, the equivalence sends a word to its restrictions to the specified groups. Empty groups and zero total size are included. This exact basis action permits simultaneous profile projections to be transported along the regrouping.
-- source:
--   Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6.SS5, Section 6.5 displayed intact tensor; general finite tensor-algebra regrouping underlying that factorization.

import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_kronFin_mode_pi_basis
open MME MME.TensorObj PiTensorProduct Module
set_option autoImplicit false
universe u

theorem mme_kronPow_fiber_grouping_preserves_tensor_and_basis {K : Type u} [Field K] {d N k : ℕ}
    (T : TensorObj K d) {I : Fin d → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) (count : Fin k → ℕ)
    (positions : Fin N ≃ (Σ j, Fin (count j))) :
    ∃ Φ : ∀ i, (T.kronPow N).V i ≃ₗ[K]
        (kronFin k (fun j ↦ T.kronPow (count j))).V i,
      PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) (T.kronPow N).t =
        (kronFin k (fun j ↦ T.kronPow (count j))).t ∧
      ∀ i (w : Fin N → I i),
        Φ i (kronPowModeWordBasis T i (b i) N w) =
          kronFinModePiBasis k (fun j ↦ T.kronPow (count j)) i
            (fun j ↦ kronPowModeWordBasis T i (b i) (count j))
            (fun j r ↦ w (positions.symm ⟨j, r⟩))  := by sorry
