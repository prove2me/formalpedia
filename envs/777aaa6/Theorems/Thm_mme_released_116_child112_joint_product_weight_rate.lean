-- Prove2me | Theorems.Thm_mme_released_116_child112_joint_product_weight_rate
-- name    : mme_released_116_child112_joint_product_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:04:30.510534+00:00
-- url     : https://prove2.me/theorems/7e5ccc41-a114-4e38-8c01-b8ffe7b7ef45
-- title:
--   Joint product extraction rate for the six physical released 112 cells
-- statement:
--   For every positive delta, all sufficiently large even replications admit an actual matrix extraction from the six-symmetrization of the product of all six physical released 112 cells. The copy count is positive. For every field and real tau, the total matrix tau-weight is at least the exponential of the sum of the six certified regional entropy-plus-volume rates. The source uses the exact split-count lengths and integerProfile histograms. Finite tensor-product assembly preserves the full product weight, and six-symmetrization commutes with the regional product by an actual tensor isomorphism. Boundary cells and the global fourth-power source are not asserted by this component theorem.
-- source:
--   Exact released integer profiles and constructive coupled-family extraction.

import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_finite_MM_extraction_swap_double
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Theorems.Thm_mme_complete_split_112_outer_star_entropy_rate
import Theorems.Thm_mme_central_binomial_sqrt_loss_log_rate
import Definitions.Def_mme_complete_split_112_address_words
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Theorems.Thm_mme_primary_hash_uniform_stars_joint_directional_capacity
import Theorems.Thm_mme_complete_split_112_coupled_restricted_family_certificate
import Theorems.Thm_mme_complete_split_112_canonical_profile_router
import Theorems.Thm_mme_complete_split_112_canonical_power_restricts_from_intact
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Definitions.Def_mme_released_116_integer_profiles
open MME MME.CompleteSplit MME.RecursiveYZ MME.Released116
open MME.MoreAsymmetryExactSeed
open MME.Released116 MME.CompleteSplit112 Filter
open BigOperators
set_option autoImplicit false
universe u

theorem mme_released_116_child112_joint_product_weight_rate
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ (K : Type u) [Field K] (tau : ℝ),
      ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
          (sixSymmetrization (TensorObj.kronFin 6 (fun r =>
            CWCells.unbroken K 5 2
              ((2 * k) * (splitCount r (⟨![1, 1, 2], by decide⟩ : Split) +
                splitCount r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))))
              (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
              (fun i _ w => (2 * k) * integerProfile i ⟨r, (⟨![1, 1, 2], by decide⟩ : Split)⟩ w)))) ∧
        Real.exp (∑ r : Fin 6,
          let s := (seed.region.getD r.val 0 *
            (splitWeight r (⟨![1, 1, 2], by decide⟩ : Split) +
              splitWeight r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))) * denominator)
          let N := denominator * (k * s)
          let L := (2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2)) * (k * s)
          let G := (denominator - 2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2)) * (k * s)
          let p : ℝ := ((((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2) : ℝ) / denominator
          ((4 * N : ℕ) : ℝ) *
            (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
          ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5) ≤
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by sorry
