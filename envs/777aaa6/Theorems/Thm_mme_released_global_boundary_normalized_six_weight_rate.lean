-- Prove2me | Theorems.Thm_mme_released_global_boundary_normalized_six_weight_rate
-- name    : mme_released_global_boundary_normalized_six_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T03:03:58.846103+00:00
-- url     : https://prove2.me/theorems/746b86d7-77ed-45a2-8731-7956d7cc6605
-- title:
--   Released boundary windows attain six-symmetric matrix weight
-- statement:
--   Each positive-mass global boundary cell admits a positive square-matrix extraction from its sixfold-symmetrized normalized window. Its tau weight eventually attains six times tau times the exact histogram entropy and CW-letter rate, uniformly over nonnegative tolerance and tau.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_sixSymmetrization_restrict
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_released_global_frame_data
import Theorems.Thm_mme_basis_projected_family_restrict
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj MME.RecursiveYZ.Boundary
open Filter
open BigOperators MME MME.TensorObj MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_boundary_normalized_six_weight_rate
    (owner : Fin 6) (c : Cell 8 1 (fun _ _ ↦ 8))
    (hmass : 0 < coarseCounts owner c.2) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 3
        (coarseCounts owner c.2),
      (∀ i w, wordCounts owner i c.2 w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ M : ℕ, 0 < M ∧
        (∀ (eps : ℝ), 0 ≤ eps → ∀ (K : Type u) [Field K],
          let L := k * coarseCounts owner c.2
          Restrict (MMObj K M M M) (sixSymmetrization
      ((source K 5 3 L).basisAllAllowedSubtensor (basis K 5 3 L) (fun i x =>
        (∀ r, CWCells.grade (label 5 3 L (Equiv.refl _) x r) = (c.2.val i).val) ∧
        if L = 0 then ∀ w, |(profile owner).2 i c w| ≤ eps else
        ∀ w, |(count (fun _ : Fin L => Unit.unit)
          (label 5 3 L (Equiv.refl _) x) Unit.unit w : ℝ) / (L : ℝ) -
          ((blocks k : ℝ) / (L : ℝ)) * (profile owner).2 i c w| ≤
          ((blocks k : ℝ) / (L : ℝ)) * eps)))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (6 * tau * ((k : ℝ) *
            (((coarseCounts owner c.2 : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ (B.count w : ℝ) /
                  ((coarseCounts owner c.2 : ℕ) : ℝ)) +
              ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by sorry
