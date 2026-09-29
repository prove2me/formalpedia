-- Prove2me | Theorems.Thm_mme_released_116_parent_child_matrix_weight_rate
-- name    : mme_released_116_parent_child_matrix_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:55:15.136643+00:00
-- url     : https://prove2.me/theorems/0c44ee88-2a59-4774-ad1f-30f2c70643e7
-- title:
--   Released parent windows admit matrix families with the combined child weight
-- statement:
--   For any positive rate allowance and nonnegative tau, sufficiently small positive tolerances admit cofinally many even released 116 parent replications with actual matrix-family restrictions from their six-symmetrized graded histogram windows. The weight retains the full sixth power of the positive surviving parent copy count times the explicit combined boundary and interior exponential rate. The statement retains the parent repair bounds and exact output predicate. Parent and child extractions are constructed rather than assumed. The global matrix multiplication exponent surplus remains a separate obligation.
-- source:
--   Cofinal even parent survival composed with the released profiled-output child rate and exact sixth-power multiplicity.

import Theorems.Thm_mme_regional_entropy_uniform_modulus
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_released_116_regional_split_mass
import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_released_116_integer_profile_support
import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Definitions.Def_mme_regional_entropy_copy_bound
import Mathlib.Tactic.Ring
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_mme_regional_physical_hash_load_entropy_bounds
import Theorems.Thm_mme_common_hash_scale_real_upper_bound
import Theorems.Thm_mme_regional_target_entropy_bounds
import Theorems.Thm_mme_entropy_retention_lower_bound
import Mathlib
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Definitions.Def_mme_recursive_profiled_CW_data
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import Theorems.Thm_mme_released_116_regional_total
import Theorems.Thm_mme_released_116_weighted_parent_center
import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fin.Basic
import Theorems.Thm_mme_recursive_region_computed_hash_selection
import Theorems.Thm_mme_recursive_region_derived_parent_hole_budget
import Mathlib.Data.Nat.Log
import Theorems.Thm_mme_released_116_scaled_reference_exists
import Theorems.Thm_mme_released_116_scaled_integer_divisibility
import Theorems.Thm_mme_released_116_integer_profile_boundary
import Theorems.Thm_mme_released_116_integer_profile_mass
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_mme_recursive_yz_CW_cells
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Definitions.Def_mme_mmobj_mul
import Theorems.Thm_mme_recursive_yz_actual_cell_product_restriction
import Definitions.Def_mme_recursive_x_hash_families
import Definitions.Def_mme_recursive_yz_physical_words
import Theorems.Thm_mme_basis_projected_family_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
open BigOperators MME MME.RegionRate MME.RecursiveThinSplit
open BigOperators MME.RegionRate
open MME.RecursiveYZ
open scoped Classical
open MME
open BigOperators MME MME.RecursiveThinSplit
open BigOperators MME MME.RegionRate
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open MME.RegionRate
open BigOperators MME MME.RegionRate MME.RecursiveYZ
open Filter
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.CompleteSplit
open MME.Released116 MME.MoreAsymmetryExactSeed MME.CompleteSplit
open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open MME.ProfiledCW MME.RecursiveYZ.CWCells
open MME MME.ProfiledCW
open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.Released116 MME.MoreAsymmetryExactSeed
open Filter Topology
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ
open MME.CompleteSplit MME.ProfiledCW MME.RecursiveYZ.CWCells
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
open MME BigOperators
open MME MME.CompleteSplit MME.RecursiveYZ MME.Released116
open MME.MoreAsymmetryExactSeed
open MME.Released116 MME.CompleteSplit112 Filter
open BigOperators
open MME MME.RecursiveYZ MME.Released116
open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.TensorObj
open MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ
open MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false
universe u

theorem mme_released_116_parent_child_matrix_weight_rate
    {KField : Type u} [Field KField]
    (delta : ℝ) (hdelta : 0 < delta) (tau : ℝ) (htau : 0 ≤ tau) :
    let mass (c : Cell 4 6 parent) :=
      splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)
    ∃ (e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent) (z : Fin 18 → Fin 3)
      (B : ∀ r : Fin 18, Boundary.Profile 2 (mass (e (.inl r)))),
      (∀ r, ((e (.inl r)).2.val (z r)).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      (∀ r i w, integerProfile i (e (.inl r)) w = (B r).mu (z r) i w) ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
    ∃ d : ℕ, 1 < d ∧ ∀ K : ℕ,
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧
    let n := fun r : Fin 6 => k * regionalSize r
    let m := fun r c => k * splitCount r c
    let mu := fun i c w => k * integerProfile i c w
    let source : Predicate ((k * denominator ^ 4) * 4) := fun i x =>
      (∀ p : Fin (k * denominator ^ 4),
        (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p q).val) = parent 0 i) ∧
      ∀ w : CompleteWord 3,
        |(Fintype.card {p : Fin (k * denominator ^ 4) //
            ProfiledCW.split (ell := 3) (Equiv.refl _) rfl x p = w} : ℝ) /
            (k * denominator ^ 4 : ℕ) -
          ((((ReleasedGlobal.jointRows 0 10).map
            (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
            (denominator : ℝ) ^ 4| ≤ eps
    let keep := fun (i : Fin 2) (_ : Address 4 6 parent n) =>
      parentTypical parent_total n m (mu (yzMode i)) eps
    let Q := commonScale 4 (loadNum parent_total m d (fun i => mu (yzMode i)) keep) (loadDen m)
    ∃ (positions : Fin ((k * denominator ^ 4) * 2) ≃ Position n)
      (reference : Address 4 6 parent n), reference ∈ RecursiveXHash.target m ∧
      ∃ E : ExactStep 2 ((k * denominator ^ 4) * 4) source,
        0 < E.copies ∧
        ((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell parent_total reference)
            (fun c i => (c.2.val i).val) mu i)) + 1 ∧
        Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤
          Real.log 8 + (1 / 80 : ℝ) * (4 * (k * denominator ^ 4) : ℕ) ∧
        (E.output = fun i x => Graded parent_total i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell parent_total reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x) ) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin E.copies => tensor KField E.output))
          (tensor KField source) ∧
        (((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q)) /
          (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies ∧
        ∃ t : ℕ, k = 2 * t ∧
        ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun v : Fin (E.copies ^ 6 * copies) =>
              let j := (finProdFinEquiv.symm v).2
              MMObj KField (a j) (b j) (c j)))
            (sixSymmetrization (tensor KField source)) ∧
          (E.copies : ℝ) ^ 6 * Real.exp ((∑ r : Fin 18, 6 * tau * (((2 * t : ℕ) : ℝ) *
            ((mass (e (.inl r)) : ℝ) * Real.log 2 * mme_modern_entropyBits
              (fun w ↦ ((B r).count w : ℝ) / (mass (e (.inl r)) : ℝ)) +
              ((∑ w, (B r).count w * ones w : ℕ) : ℝ) * Real.log 5 - delta))) +
            (∑ r : Fin 6,
          let s := (seed.region.getD r.val 0 *
            (splitWeight r (⟨![1, 1, 2], by decide⟩ : Split) +
              splitWeight r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))) * denominator)
          let N := denominator * (t * s)
          let L := (2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2)) * (t * s)
          let G := (denominator - 2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2)) * (t * s)
          let p : ℝ := ((((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
            (0, [], 0)).2.2) : ℝ) / denominator
          ((4 * N : ℕ) : ℝ) *
            (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
          ((6 * (4 * G + 2 * L) : ℕ) : ℝ) * tau * Real.log 5)) ≤
            ∑ v : Fin (E.copies ^ 6 * copies),
              let j := (finProdFinEquiv.symm v).2
              ((a j * b j * c j : ℕ) : ℝ) ^ tau := by sorry
