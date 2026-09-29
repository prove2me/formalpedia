-- Prove2me | Theorems.Thm_mme_released_116_boundary_product_weight_rate
-- name    : mme_released_116_boundary_product_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:24:22.726858+00:00
-- url     : https://prove2.me/theorems/dc191174-6fc1-4bc7-b507-bbb32fe52c23
-- title:
--   Finite released boundary families attain their joint six-symmetric weight
-- statement:
--   Every finite family of released 116 boundary cells with specified zero modes has exact base integer histogram profiles and a common replication threshold. Beyond that threshold, one positive square matrix restricts from the full six-symmetrization of the product of their physical child tensors over every field. For every nonnegative tau its volume weight is at least the exponential of the sum of the individual entropy-plus-letter rates, each with the prescribed positive tolerance. There is no additional product assembly loss.
-- source:
--   Finite product of actual six-symmetric boundary matrix extractions.

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
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_toQ_kronFin
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_six_symmetrized_tau_value
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
open MME.Released116 MME.MoreAsymmetryExactSeed
open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
open MME
open MME BigOperators
set_option autoImplicit false
universe u

theorem mme_released_116_boundary_product_weight_rate
    (n : ℕ) (c : Fin n → Cell 4 6 parent) (z : Fin n → Fin 3)
    (hz : ∀ r, ((c r).2.val (z r)).val = 0) (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : ∀ r, Boundary.Profile 2
        (splitCount (c r).1 (c r).2 +
          splitCount (c r).1 (complement (parent_total (c r).1) (c r).2)),
      (∀ r i w, integerProfile i (c r) w = (B r).mu (z r) i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ M : ℕ, 0 < M ∧
        (∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K M M M)
            (sixSymmetrization (TensorObj.kronFin n (fun r ↦ CWCells.unbroken K 5 2
              (k * (splitCount (c r).1 (c r).2 +
                splitCount (c r).1 (complement (parent_total (c r).1) (c r).2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => ((c r).2.val i).val)
              (fun i _ w => k * integerProfile i (c r) w))))) ∧
        ∀ tau : ℝ, 0 ≤ tau →
          Real.exp (∑ r, 6 * tau * ((k : ℝ) *
            (((splitCount (c r).1 (c r).2 +
                splitCount (c r).1 (complement (parent_total (c r).1) (c r).2) : ℕ) : ℝ) *
              Real.log 2 * mme_modern_entropyBits
                (fun w ↦ ((B r).count w : ℝ) /
                  ((splitCount (c r).1 (c r).2 +
                    splitCount (c r).1 (complement (parent_total (c r).1) (c r).2) : ℕ) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) ≤
            ((M * M * M : ℕ) : ℝ) ^ tau := by sorry
