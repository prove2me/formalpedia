-- Prove2me | Theorems.Thm_mme_released_116_intact_reference_weight_rate
-- name    : mme_released_116_intact_reference_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:42:39.508639+00:00
-- url     : https://prove2.me/theorems/6be94dae-cc65-4b86-b955-503de4184d6e
-- title:
--   Released intact reference tensor attains the full child weight rate
-- statement:
--   For every positive rate allowance and all sufficiently large integer k, every released 116 reference address with split counts scaled by 2*k admits a positive-copy matrix-family extraction from the six-fold symmetrization of its intact tensor. For every field and nonnegative tau, the weight is at least the exponential of the explicit combined boundary and interior rate. The theorem composes the actual full-child extraction with the exact physical-cell grouping restriction. The subsequent parent-source extraction and global exponent surplus remain separate obligations.
-- source:
--   Exact physical-cell grouping and released tensor extractions.

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
import Theorems.Thm_mme_finite_MM_extractions_kronFin_tau_product
import Theorems.Thm_mme_finite_MM_extraction_swap_double
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Definitions.Def_mme_mmobj_mul
import Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction
import Definitions.Def_mme_recursive_x_hash_families
import Definitions.Def_mme_recursive_yz_physical_words
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
open MME.Released116 MME.MoreAsymmetryExactSeed
open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
open MME
open MME BigOperators
open MME MME.CompleteSplit MME.RecursiveYZ MME.Released116
open MME.MoreAsymmetryExactSeed
open MME.Released116 MME.CompleteSplit112 Filter
open BigOperators
open MME MME.RecursiveYZ MME.Released116
open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.TensorObj
set_option autoImplicit false
universe u

theorem mme_released_116_intact_reference_weight_rate
    (delta : ℝ) (hdelta : 0 < delta) :
    let mass (c : Cell 4 6 parent) :=
      splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)
    ∃ (e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent) (z : Fin 18 → Fin 3)
      (B : ∀ r : Fin 18, Boundary.Profile 2 (mass (e (.inl r)))),
      (∀ r, ((e (.inl r)).2.val (z r)).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      (∀ r i w, integerProfile i (e (.inl r)) w = (B r).mu (z r) i w) ∧
      ∀ᶠ k : ℕ in atTop,
        ∀ (d : Fin 24 ≃ Cell 4 6 parent) (L : ℕ)
          (positions : Fin L ≃ Position (fun r : Fin 6 ↦ (2 * k) * regionalSize r))
          (reference : Address 4 6 parent (fun r ↦ (2 * k) * regionalSize r)),
          reference ∈ RecursiveXHash.target (fun r c ↦ (2 * k) * splitCount r c) →
          ∀ (K : Type u) [Field K]
          (tau : ℝ), 0 ≤ tau →
        ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
            (sixSymmetrization (CWCells.unbroken K 5 2 L positions
              (fullCell parent_total reference) (fun cell i ↦ (cell.2.val i).val)
              (fun i cell w ↦ (2 * k) * integerProfile i cell w))) ∧
          Real.exp ((∑ r : Fin 18, 6 * tau * (((2 * k : ℕ) : ℝ) *
            ((mass (e (.inl r)) : ℝ) * Real.log 2 * mme_modern_entropyBits
              (fun w ↦ ((B r).count w : ℝ) / (mass (e (.inl r)) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) +
            (∑ r : Fin 6,
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
          ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5)) ≤
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by sorry
