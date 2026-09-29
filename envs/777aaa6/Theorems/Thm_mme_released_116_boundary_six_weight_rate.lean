-- Prove2me | Theorems.Thm_mme_released_116_boundary_six_weight_rate
-- name    : mme_released_116_boundary_six_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:22:24.346712+00:00
-- url     : https://prove2.me/theorems/4c74f7c9-f5be-445a-b22e-3d10f29b07f3
-- title:
--   Released boundary cells attain six-symmetric square-matrix weight
-- statement:
--   Every released 116 boundary cell admits an exact base histogram profile. For any positive tolerance, sufficiently large replications have a positive square-matrix size M that restricts from the full six-symmetric physical child tensor over every field. For every nonnegative tau, its volume weight is at least exp(6 tau k times the base entropy-plus-letter rate minus tolerance). The same M works for all fields and all such tau.
-- source:
--   Physical boundary rate and exact full matrix symmetrization.

import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_released_116_integer_profile_boundary
import Definitions.Def_mme_recursive_yz_owned_filters
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Definitions.Def_mme_recursive_yz_boundary_data
import Theorems.Thm_mme_MMObj_cyclicSymmetrization_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_sixSymmetrization_restrict
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
open MME.Released116 MME.MoreAsymmetryExactSeed
open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
open MME
set_option autoImplicit false
universe u

theorem mme_released_116_boundary_six_weight_rate
    (c : Cell 4 6 parent) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 2
        (splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)),
      (∀ i w, integerProfile i c w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ M : ℕ, 0 < M ∧
        (∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K M M M)
            (sixSymmetrization (CWCells.unbroken K 5 2
              (k * (splitCount c.1 c.2 +
                splitCount c.1 (complement (parent_total c.1) c.2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => (c.2.val i).val)
              (fun i _ w => k * integerProfile i c w)))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (6 * tau * ((k : ℝ) *
            (((splitCount c.1 c.2 +
                splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ (B.count w : ℝ) /
                  ((splitCount c.1 c.2 +
                    splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ)) +
              ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by sorry
