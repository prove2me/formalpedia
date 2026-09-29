-- Prove2me | solution 1 for mme_released_116_parent_child_matrix_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:55:36.609726+00:00
-- url     : https://prove2.me/submissions/94be8cfb-90fe-41c5-aaac-c7b5e9f4e64c

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
universe u

namespace RateBound

namespace CoarseBound

open BigOperators MME MME.RegionRate MME.RecursiveThinSplit
set_option autoImplicit false

/-- A tangent bound for the logarithm turns an atom-size bound into an entropy bound. -/
private theorem parentChild0_mme_entropy_lower_of_scaled_atom_bound {W : Type*} [Fintype W]
    (p : W → ℝ) (a b : ℝ) (ha : 0 < a) (hp : ∀ w, 0 ≤ p w)
    (hmass : ∑ w, p w = 1) (hbound : ∀ w, p w ≤ b) :
    Real.log a + 1 - a * b ≤ entropy p := by
  have hterm (w : W) : p w * (Real.log a + 1 - a * b) ≤
      Real.negMulLog (p w) := by
    by_cases hz : p w = 0
    · simp [hz]
    · have hpos := lt_of_le_of_ne (hp w) (Ne.symm hz)
      have hlog := Real.log_le_sub_one_of_pos (mul_pos ha hpos)
      rw [Real.log_mul ha.ne' hpos.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (hp w)
      have hb := mul_le_mul_of_nonneg_left (hbound w) (mul_nonneg ha.le (hp w))
      rw [Real.negMulLog_def]
      nlinarith
  have h := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hterm w)
  simpa [entropy, ← Finset.sum_mul, hmass] using h

private theorem parentChild0_mass_entropy_lower {W : Type*} [Fintype W]
    (x : W → ℝ) (s a b : ℝ) (hs : 0 < s) (ha : 0 < a) (hx : ∀ w, 0 ≤ x w)
    (hmass : ∑ w, x w = s) (hbound : ∀ w, x w ≤ b * s) :
    s * (Real.log a + 1 - a * b) ≤ massEntropy x := by
  rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).2.1 x
    (by rw [hmass]; exact hs.ne'), hmass]
  apply mul_le_mul_of_nonneg_left _ hs.le
  apply parentChild0_mme_entropy_lower_of_scaled_atom_bound _ _ _ ha
  · intro w; exact div_nonneg (hx w) hs.le
  · rw [← Finset.sum_div, hmass, div_self hs.ne']
  · intro w; exact (div_le_iff₀ hs).2 (hbound w)

private abbrev parentChild0_Split116 := Split 4 ![1, 1, 6]
private def parentChild0_c004 : parentChild0_Split116 := ⟨![0, 0, 4], by decide⟩
private def parentChild0_c013 : parentChild0_Split116 := ⟨![0, 1, 3], by decide⟩
private def parentChild0_c103 : parentChild0_Split116 := ⟨![1, 0, 3], by decide⟩
private def parentChild0_c112 : parentChild0_Split116 := ⟨![1, 1, 2], by decide⟩

private theorem parentChild0_split_univ : (Finset.univ : Finset parentChild0_Split116) = {parentChild0_c004, parentChild0_c013, parentChild0_c103, parentChild0_c112} := by
  decide

private def parentChild0_xCounts (r : Fin 6) (j : Fin 5) : ℕ :=
  if j = 0 then Released116.splitCount r parentChild0_c004 + Released116.splitCount r parentChild0_c013
  else if j = 1 then Released116.splitCount r parentChild0_c103 + Released116.splitCount r parentChild0_c112
  else 0

private theorem parentChild0_x_counts_bound : ∀ (r : Fin 6) (j : Fin 5),
    1000000 * parentChild0_xCounts r j ≤ 500001 * Released116.regionalSize r := by
  decide +kernel

private theorem parentChild0_x_counts_mass : ∀ r : Fin 6,
    ∑ j : Fin 5, parentChild0_xCounts r j = Released116.regionalSize r := by
  decide +kernel

private theorem parentChild0_x_counts_eq (r : Fin 6) (j : Fin 5) :
    marginalCounts Released116.splitCount 0 r j = parentChild0_xCounts r j := by
  classical
  unfold marginalCounts
  change (∑ c : {c : parentChild0_Split116 // c.val 0 = j}, Released116.splitCount r c.val) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c : parentChild0_Split116 => c.val 0 = j))
    (fun c => by simp) (Released116.splitCount r), Finset.sum_filter, parentChild0_split_univ]
  fin_cases j <;> norm_num [parentChild0_c004, parentChild0_c013, parentChild0_c103, parentChild0_c112, parentChild0_xCounts, add_assoc]

/-- The released X-coordinate entropy is at least 0.69 per parent occurrence.
The proof uses exact integer histogram bounds and the elementary logarithm inequality. -/
private theorem parentChild0_mme_released_116_coarse_rate_lower :
    (69 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      coarsePotential Released116.splitCount 0 := by
  unfold coarsePotential
  simp only [parentChild0_x_counts_eq]
  have hr (r : Fin 6) :
      (Released116.regionalSize r : ℝ) * (Real.log 2 + 1 - 2 * (500001 / 1000000 : ℝ)) ≤
        massEntropy (fun j => (parentChild0_xCounts r j : ℝ)) := by
    apply parentChild0_mass_entropy_lower
    · exact_mod_cast (mme_released_116_regional_split_mass r).1
    · norm_num
    · intro j; exact Nat.cast_nonneg _
    · exact_mod_cast parentChild0_x_counts_mass r
    · intro j
      have h : (1000000 : ℝ) * parentChild0_xCounts r j ≤ 500001 * Released116.regionalSize r := by
        exact_mod_cast parentChild0_x_counts_bound r j
      linarith
  have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hr r)
  rw [← Finset.sum_mul, ← Nat.cast_sum] at h
  have hlog : (69 / 100 : ℝ) ≤ Real.log 2 + 1 - 2 * (500001 / 1000000 : ℝ) := by
    have := Real.log_two_gt_d9
    linarith
  rw [mul_comm]
  exact (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)).trans h


end CoarseBound

namespace ParentBound

open BigOperators MME MME.RegionRate MME.RecursiveThinSplit
set_option autoImplicit false

/-- A tangent bound for the logarithm turns an atom-size bound into an entropy bound. -/
private theorem parentChild0_mme_entropy_lower_of_scaled_atom_bound {W : Type*} [Fintype W]
    (p : W → ℝ) (a b : ℝ) (ha : 0 < a) (hp : ∀ w, 0 ≤ p w)
    (hmass : ∑ w, p w = 1) (hbound : ∀ w, p w ≤ b) :
    Real.log a + 1 - a * b ≤ entropy p := by
  have hterm (w : W) : p w * (Real.log a + 1 - a * b) ≤
      Real.negMulLog (p w) := by
    by_cases hz : p w = 0
    · simp [hz]
    · have hpos := lt_of_le_of_ne (hp w) (Ne.symm hz)
      have hlog := Real.log_le_sub_one_of_pos (mul_pos ha hpos)
      rw [Real.log_mul ha.ne' hpos.ne'] at hlog
      have hmul := mul_le_mul_of_nonneg_left hlog (hp w)
      have hb := mul_le_mul_of_nonneg_left (hbound w) (mul_nonneg ha.le (hp w))
      rw [Real.negMulLog_def]
      nlinarith
  have h := Finset.sum_le_sum (fun w (_ : w ∈ Finset.univ) => hterm w)
  simpa [entropy, ← Finset.sum_mul, hmass] using h

private abbrev parentChild0_Word := CompleteSplit.CompleteWord 2
private abbrev parentChild0_Split116 := Split 4 ![1, 1, 6]
private def parentChild0_c004 : parentChild0_Split116 := ⟨![0, 0, 4], by decide⟩
private def parentChild0_c013 : parentChild0_Split116 := ⟨![0, 1, 3], by decide⟩
private def parentChild0_c103 : parentChild0_Split116 := ⟨![1, 0, 3], by decide⟩
private def parentChild0_c112 : parentChild0_Split116 := ⟨![1, 1, 2], by decide⟩

private theorem parentChild0_split_univ : (Finset.univ : Finset parentChild0_Split116) = {parentChild0_c004, parentChild0_c013, parentChild0_c103, parentChild0_c112} := by
  decide

private theorem parentChild0_split_sum (f : parentChild0_Split116 → ℝ) :
    ∑ c, f c = f parentChild0_c004 + f parentChild0_c013 + f parentChild0_c103 + f parentChild0_c112 := by
  rw [parentChild0_split_univ]
  norm_num [parentChild0_c004, parentChild0_c013, parentChild0_c103, parentChild0_c112, add_assoc]

private def parentChild0_frequencyQ (i : Fin 3) (r : Fin 6) (c : parentChild0_Split116) (w : parentChild0_Word) : ℚ :=
  (Released116.integerProfile i ⟨r, c⟩ w : ℚ) /
    (∑ v : parentChild0_Word, Released116.integerProfile i ⟨r, c⟩ v : ℕ)

private def parentChild0_mixtureQ (i : Fin 3) (r : Fin 6) (w : Fin 2 → parentChild0_Word) : ℚ :=
  ((Released116.splitCount r parentChild0_c004 : ℚ) * parentChild0_frequencyQ i r parentChild0_c004 (w 0) * parentChild0_frequencyQ i r parentChild0_c112 (w 1) +
   (Released116.splitCount r parentChild0_c013 : ℚ) * parentChild0_frequencyQ i r parentChild0_c013 (w 0) * parentChild0_frequencyQ i r parentChild0_c103 (w 1) +
   (Released116.splitCount r parentChild0_c103 : ℚ) * parentChild0_frequencyQ i r parentChild0_c103 (w 0) * parentChild0_frequencyQ i r parentChild0_c013 (w 1) +
   (Released116.splitCount r parentChild0_c112 : ℚ) * parentChild0_frequencyQ i r parentChild0_c112 (w 0) * parentChild0_frequencyQ i r parentChild0_c004 (w 1)) /
    Released116.regionalSize r

private theorem parentChild0_frequencyQ_cast (i : Fin 3) (r : Fin 6) (c : parentChild0_Split116) (w : parentChild0_Word) :
    (parentChild0_frequencyQ i r c w : ℝ) = RegionRealization.cellFrequency
      (Released116.integerProfile i) ⟨r, c⟩ w := by
  simp [parentChild0_frequencyQ, RegionRealization.cellFrequency]

private theorem parentChild0_mixtureQ_cast (i : Fin 3) (r : Fin 6) (w : Fin 2 → parentChild0_Word) :
    (parentChild0_mixtureQ i r w : ℝ) = RegionRealization.parentMixture Released116.parent_total
      Released116.regionalSize Released116.splitCount (Released116.integerProfile i) r w := by
  unfold RegionRealization.parentMixture
  change _ = (∑ c : parentChild0_Split116, (Released116.splitCount r c : ℝ) *
    RegionRealization.cellFrequency (Released116.integerProfile i) ⟨r, c⟩ (w 0) *
    RegionRealization.cellFrequency (Released116.integerProfile i)
      ⟨r, RecursiveYZ.complement (Released116.parent_total r) c⟩ (w 1)) / _
  rw [parentChild0_split_sum]
  have h004 : RecursiveYZ.complement (Released116.parent_total r) parentChild0_c004 = parentChild0_c112 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  have h013 : RecursiveYZ.complement (Released116.parent_total r) parentChild0_c013 = parentChild0_c103 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  have h103 : RecursiveYZ.complement (Released116.parent_total r) parentChild0_c103 = parentChild0_c013 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  have h112 : RecursiveYZ.complement (Released116.parent_total r) parentChild0_c112 = parentChild0_c004 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  simp only [parentChild0_mixtureQ, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    parentChild0_frequencyQ_cast, h004, h013, h103, h112]

private theorem parentChild0_mixtureQ_y_bounds : ∀ (r : Fin 6) (w : Fin 2 → parentChild0_Word),
    0 ≤ parentChild0_mixtureQ 1 r w ∧ parentChild0_mixtureQ 1 r w ≤ 250001 / 1000000 := by
  decide +kernel

private theorem parentChild0_mixtureQ_y_mass : ∀ r : Fin 6, ∑ w : Fin 2 → parentChild0_Word, parentChild0_mixtureQ 1 r w = 1 := by
  decide +kernel

private theorem parentChild0_mixtureQ_z_bounds : ∀ (r : Fin 6) (w : Fin 2 → parentChild0_Word),
    0 ≤ parentChild0_mixtureQ 2 r w ∧ parentChild0_mixtureQ 2 r w ≤ 193 / 1000 := by
  decide +kernel

private theorem parentChild0_mixtureQ_z_mass : ∀ r : Fin 6, ∑ w : Fin 2 → parentChild0_Word, parentChild0_mixtureQ 2 r w = 1 := by
  decide +kernel

private theorem parentChild0_parent_lower (i : Fin 3) (b : ℚ) (L : ℝ)
    (hbound : ∀ (r : Fin 6) (w : Fin 2 → parentChild0_Word), 0 ≤ parentChild0_mixtureQ i r w ∧ parentChild0_mixtureQ i r w ≤ b)
    (hmass : ∀ r : Fin 6, ∑ w : Fin 2 → parentChild0_Word, parentChild0_mixtureQ i r w = 1)
    (hlog : L ≤ Real.log 4 + 1 - 4 * (b : ℝ)) :
    L * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      parentPotential Released116.parent_total Released116.regionalSize
        Released116.splitCount (Released116.integerProfile i) := by
  have hr (r : Fin 6) :
      L ≤ entropy (RegionRealization.parentMixture Released116.parent_total
        Released116.regionalSize Released116.splitCount (Released116.integerProfile i) r) := by
    apply hlog.trans
    apply parentChild0_mme_entropy_lower_of_scaled_atom_bound _ 4 (b : ℝ) (by norm_num)
    · intro w
      rw [← parentChild0_mixtureQ_cast]
      exact_mod_cast (hbound r w).1
    · simp_rw [← parentChild0_mixtureQ_cast]
      exact_mod_cast hmass r
    · intro w
      rw [← parentChild0_mixtureQ_cast]
      exact_mod_cast (hbound r w).2
  have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hr r) (Nat.cast_nonneg (Released116.regionalSize r)))
  rw [← Finset.sum_mul, ← Nat.cast_sum] at h
  simpa only [parentPotential, mul_comm L] using h

private theorem parentChild0_log_four : Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  exact h

/-- The actual released Y parent mixtures have at least 1.38 natural-log entropy
per parent occurrence, certified from their exact rational atoms. -/
private theorem parentChild0_mme_released_116_parent_y_entropy_lower :
    (138 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      parentPotential Released116.parent_total Released116.regionalSize
        Released116.splitCount (Released116.integerProfile 1) := by
  apply parentChild0_parent_lower 1 (250001 / 1000000) _ parentChild0_mixtureQ_y_bounds parentChild0_mixtureQ_y_mass
  rw [parentChild0_log_four]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have := Real.log_two_gt_d9
  linarith

/-- The actual released Z parent mixtures have at least 1.6 natural-log entropy
per parent occurrence, certified from their exact rational atoms. -/
private theorem parentChild0_mme_released_116_parent_z_entropy_lower :
    (160 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      parentPotential Released116.parent_total Released116.regionalSize
        Released116.splitCount (Released116.integerProfile 2) := by
  apply parentChild0_parent_lower 2 (193 / 1000) _ parentChild0_mixtureQ_z_bounds parentChild0_mixtureQ_z_mass
  rw [parentChild0_log_four]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have := Real.log_two_gt_d9
  linarith


end ParentBound

namespace CompatibilityBound

open BigOperators MME.RegionRate
set_option autoImplicit false

/-- A probability distribution supported on at most k atoms has entropy at most log k. -/
private theorem parentChild0_mme_entropy_upper_of_support_card {W : Type*} [Fintype W]
    (p : W → ℝ) (S : Finset W) (k : ℕ) (hk : 0 < k)
    (hp : ∀ w, 0 ≤ p w) (hmass : ∑ w, p w = 1)
    (hsupp : ∀ w, w ∉ S → p w = 0) (hcard : S.card ≤ k) :
    entropy p ≤ Real.log k := by
  classical
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hterm (w : W) : Real.negMulLog (p w) ≤
      p w * Real.log k + (k : ℝ)⁻¹ - p w := by
    by_cases hz : p w = 0
    · simp [hz, inv_nonneg.mpr hk'.le]
    · have hpos := lt_of_le_of_ne (hp w) (Ne.symm hz)
      have hlog := Real.log_le_sub_one_of_pos (div_pos (inv_pos.mpr hk') hpos)
      rw [Real.log_div (inv_ne_zero hk'.ne') hz, Real.log_inv] at hlog
      have h := mul_le_mul_of_nonneg_left hlog (hp w)
      have he : p w * ((k : ℝ)⁻¹ / p w) = (k : ℝ)⁻¹ := by field_simp
      simp only [mul_sub, he, mul_one] at h
      rw [Real.negMulLog_def]
      nlinarith
  have hmassS : ∑ w ∈ S, p w = 1 := by
    rw [← hmass]
    exact Finset.sum_subset (Finset.subset_univ _) (fun w _ hw => hsupp w hw)
  have hsum : entropy p = ∑ w ∈ S, Real.negMulLog (p w) := by
    unfold entropy
    exact (Finset.sum_subset (Finset.subset_univ _) (fun w _ hw => by simp [hsupp w hw])).symm
  rw [hsum]
  have h := Finset.sum_le_sum (fun w (_ : w ∈ S) => hterm w)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    hmassS, one_mul, Finset.sum_const, nsmul_eq_mul] at h
  have hc : (S.card : ℝ) * (k : ℝ)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hk']
    exact_mod_cast hcard
  linarith

/-- Homogeneous entropy obeys the same support-cardinality bound, including empty histograms. -/
private theorem parentChild0_mme_mass_entropy_upper_of_support_card {W : Type*} [Fintype W]
    (mu : W → ℕ) (S : Finset W) (k : ℕ) (hk : 0 < k)
    (hsupp : ∀ w, w ∉ S → mu w = 0) (hcard : S.card ≤ k) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * Real.log k := by
  classical
  by_cases hz : ∑ w, mu w = 0
  · have hw : ∀ w, mu w = 0 := fun w => Finset.sum_eq_zero_iff.mp hz w (Finset.mem_univ _)
    simp [hw, massEntropy, entropy]
  · have hs : (∑ w, (mu w : ℝ)) ≠ 0 := by exact_mod_cast hz
    rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).2.1 _ hs]
    simp only [← Nat.cast_sum]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply parentChild0_mme_entropy_upper_of_support_card _ S k hk
    · intro w; positivity
    · rw [← Finset.sum_div, ← Nat.cast_sum, div_self (by exact_mod_cast hz)]
    · intro w hw; simp [hsupp w hw]
    · exact hcard


private abbrev parentChild0_Word := MME.CompleteSplit.CompleteWord 2
private def parentChild0_gradeSupport (j : Fin 5) : Finset parentChild0_Word :=
  Finset.univ.filter (fun w => ∑ h, (w h).val = j.val)

private theorem parentChild0_grade_card : ∀ j : Fin 5,
    (parentChild0_gradeSupport j).card ≤ 2 ^ j.val ∧ (parentChild0_gradeSupport j).card ≤ 2 ^ (4 - j.val) := by
  decide +kernel

private theorem parentChild0_grade_entropy_upper (mu : parentChild0_Word → ℕ) (j : Fin 5)
    (hsupp : ∀ w, 0 < mu w → ∑ h, (w h).val = j.val) (d : ℕ)
    (hcard : (parentChild0_gradeSupport j).card ≤ 2 ^ d) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * d * Real.log 2 := by
  have h := parentChild0_mme_mass_entropy_upper_of_support_card mu (parentChild0_gradeSupport j) (2 ^ d)
    (by positivity) (fun w hw => by
      by_contra hn
      have hg := hsupp w (Nat.pos_of_ne_zero hn)
      exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)) hcard
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_assoc] using h

/-- A two-symbol child histogram of grade j has at most 2^j possible words. -/
private theorem parentChild0_mme_complete_word_two_low_grade_entropy_upper
    (mu : MME.CompleteSplit.CompleteWord 2 → ℕ) (j : Fin 5)
    (hsupp : ∀ w, 0 < mu w → ∑ h, (w h).val = j.val) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * j.val * Real.log 2 := by
  exact parentChild0_grade_entropy_upper mu j hsupp j.val (parentChild0_grade_card j).1

/-- Reversing the word grades gives the sharper bound for high-grade children. -/
private theorem parentChild0_mme_complete_word_two_high_grade_entropy_upper
    (mu : MME.CompleteSplit.CompleteWord 2 → ℕ) (j : Fin 5)
    (hsupp : ∀ w, 0 < mu w → ∑ h, (w h).val = j.val) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * (4 - j.val : ℕ) * Real.log 2 := by
  exact parentChild0_grade_entropy_upper mu j hsupp (4 - j.val) (parentChild0_grade_card j).2

open MME.RecursiveYZ
open scoped Classical

private theorem parentChild0_part_weighted_count {C W G : Type*} [Fintype C] [Fintype G]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ) (d : G → ℕ) (w : W) :
    ∑ s : {c : C // boundary c} ⊕ G,
      partCount boundary group mu s w * (s.elim (fun c => d (group c.val)) d) =
        ∑ c, mu c w * d (group c) := by
  simp only [Fintype.sum_sum_type, partCount, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.sum_subtype (Finset.univ.filter boundary) (fun c => by simp)
    (fun c => mu c w * d (group c)), Finset.sum_filter]
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : boundary c <;> simp [hc]

private theorem parentChild0_part_weighted_mass {C W G : Type*} [Fintype C] [Fintype G] [Fintype W]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ) (d : G → ℕ) :
    ∑ s : {c : C // boundary c} ⊕ G,
      (∑ w, partCount boundary group mu s w) * (s.elim (fun c => d (group c.val)) d) =
        ∑ c, (∑ w, mu c w) * d (group c) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [parentChild0_part_weighted_count]
  rw [Finset.sum_comm]

open MME

private abbrev parentChild0_Parts (i : Fin 2) :=
  {c : Cell 4 6 Released116.parent // yzBoundary i c} ⊕ (Fin 6 × Fin 5)

private def parentChild0_partGrade (i : Fin 2) (s : parentChild0_Parts i) : Fin 5 :=
  s.elim (fun c => c.val.2.val (yzMode i)) Prod.snd

private theorem parentChild0_part_support (i : Fin 2) (s : parentChild0_Parts i) (w : parentChild0_Word)
    (h : 0 < partCount (yzBoundary i) (modeGroup (yzMode i))
      (Released116.integerProfile (yzMode i)) s w) :
    ∑ a, (w a).val = (parentChild0_partGrade i s).val := by
  cases s with
  | inl c => exact mme_released_116_integer_profile_support (yzMode i) c.val w h
  | inr g =>
    dsimp [partCount] at h
    obtain ⟨c, _, hc⟩ := Finset.sum_pos_iff.mp h
    split_ifs at hc with hcg
    · have hs := mme_released_116_integer_profile_support (yzMode i) c w hc
      have hg := congrArg (fun t : Fin 6 × Fin 5 => t.2.val) hcg.2
      exact hs.trans hg
    · omega

private theorem parentChild0_released_weighted_y_mass :
    ∑ c : Cell 4 6 Released116.parent,
      (∑ w, Released116.integerProfile 1 c w) * (modeGroup 1 c).2.val =
        ∑ r, Released116.regionalSize r := by
  decide +kernel

private theorem parentChild0_released_weighted_z_mass :
    ∑ c : Cell 4 6 Released116.parent,
      (∑ w, Released116.integerProfile 2 c w) * (4 - (modeGroup 2 c).2.val) =
        2 * ∑ r, Released116.regionalSize r := by
  decide +kernel

/-- The compatibility partition retains Y grades, whose total is one per parent. -/
private theorem parentChild0_mme_released_116_compatibility_y_entropy_upper :
    compatibilityPotential 0 (Released116.integerProfile 1) ≤
      ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) * Real.log 2 := by
  unfold compatibilityPotential
  rw [(mme_regional_mass_entropy_algebra (C := parentChild0_Parts 0) (W := parentChild0_Word)).2.2]
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    parentChild0_mme_complete_word_two_low_grade_entropy_upper
      (partCount (yzBoundary 0) (modeGroup (yzMode 0))
        (Released116.integerProfile (yzMode 0)) s)
      (parentChild0_partGrade 0 s) (parentChild0_part_support 0 s))
  refine h.trans_eq ?_
  rw [← Finset.sum_mul]
  have hm := parentChild0_part_weighted_mass (yzBoundary (half := 4) (parent := Released116.parent) 0)
    (modeGroup (yzMode 0)) (Released116.integerProfile (yzMode 0)) (fun g => g.2.val)
  have he (s : parentChild0_Parts 0) :
      s.elim (fun c => (modeGroup (yzMode 0) c.val).2.val) (fun g => g.2.val) =
        (parentChild0_partGrade 0 s).val := by cases s <;> rfl
  simp only [he] at hm
  have ht : (∑ s : parentChild0_Parts 0, (∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0))
    (Released116.integerProfile (yzMode 0)) s w) * (parentChild0_partGrade 0 s).val) =
      ∑ r, Released116.regionalSize r := hm.trans parentChild0_released_weighted_y_mass
  congr 1
  exact_mod_cast ht

/-- The complementary Z grade totals two per parent, bounding compatibility entropy. -/
private theorem parentChild0_mme_released_116_compatibility_z_entropy_upper :
    compatibilityPotential 1 (Released116.integerProfile 2) ≤
      (2 * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ)) * Real.log 2 := by
  unfold compatibilityPotential
  rw [(mme_regional_mass_entropy_algebra (C := parentChild0_Parts 1) (W := parentChild0_Word)).2.2]
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    parentChild0_mme_complete_word_two_high_grade_entropy_upper
      (partCount (yzBoundary 1) (modeGroup (yzMode 1))
        (Released116.integerProfile (yzMode 1)) s)
      (parentChild0_partGrade 1 s) (parentChild0_part_support 1 s))
  refine h.trans_eq ?_
  rw [← Finset.sum_mul]
  have hm := parentChild0_part_weighted_mass (yzBoundary (half := 4) (parent := Released116.parent) 1)
    (modeGroup (yzMode 1)) (Released116.integerProfile (yzMode 1)) (fun g => 4 - g.2.val)
  have he (s : parentChild0_Parts 1) :
      s.elim (fun c => 4 - (modeGroup (yzMode 1) c.val).2.val) (fun g => 4 - g.2.val) =
        4 - (parentChild0_partGrade 1 s).val := by cases s <;> rfl
  simp only [he] at hm
  have ht : (∑ s : parentChild0_Parts 1, (∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1))
    (Released116.integerProfile (yzMode 1)) s w) * (4 - (parentChild0_partGrade 1 s).val)) =
      2 * ∑ r, Released116.regionalSize r := hm.trans parentChild0_released_weighted_z_mass
  congr 1
  exact_mod_cast ht


end CompatibilityBound

namespace PenaltyBound

open BigOperators MME MME.RecursiveThinSplit
set_option autoImplicit false

private abbrev parentChild0_Split116 := Split 4 ![1, 1, 6]
private def parentChild0_c004 : parentChild0_Split116 := ⟨![0, 0, 4], by decide⟩
private def parentChild0_c013 : parentChild0_Split116 := ⟨![0, 1, 3], by decide⟩
private def parentChild0_c103 : parentChild0_Split116 := ⟨![1, 0, 3], by decide⟩
private def parentChild0_c112 : parentChild0_Split116 := ⟨![1, 1, 2], by decide⟩

private theorem parentChild0_split_univ : (Finset.univ : Finset parentChild0_Split116) = {parentChild0_c004, parentChild0_c013, parentChild0_c103, parentChild0_c112} := by
  decide

private theorem parentChild0_split_sum (f : parentChild0_Split116 → ℝ) :
    ∑ c, f c = f parentChild0_c004 + f parentChild0_c013 + f parentChild0_c103 + f parentChild0_c112 := by
  rw [parentChild0_split_univ]
  norm_num [parentChild0_c004, parentChild0_c013, parentChild0_c103, parentChild0_c112, add_assoc]

private theorem parentChild0_marginal_sum (f : parentChild0_Split116 → ℝ) (i : Fin 3) (j : Fin 5) :
    mme_modern_marginal (fun c : parentChild0_Split116 => c.val i) f j =
      ∑ c, if c.val i = j then f c else 0 := by
  unfold mme_modern_marginal
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c : parentChild0_Split116 => c.val i = j))
    (fun c => by simp) f, Finset.sum_filter]

/-- The three coordinate marginals determine a distribution on the four
splits of the (1,1,6) component. The extreme third-coordinate entries recover
004 and 112; the first two marginals then recover 103 and 013. -/
private theorem parentChild0_mme_116_split_marginals_injective (alpha rho : Split 4 ![1, 1, 6] → ℝ)
    (h : ∀ (i : Fin 3) (j : Fin 5),
      mme_modern_marginal (fun c : Split 4 ![1, 1, 6] => c.val i) rho j =
        mme_modern_marginal (fun c : Split 4 ![1, 1, 6] => c.val i) alpha j) :
    rho = alpha := by
  have h004 := h 2 4
  have h112 := h 2 2
  have h103 := h 0 1
  have h013 := h 1 1
  simp only [parentChild0_marginal_sum, parentChild0_split_sum] at h004 h112 h103 h013
  change rho parentChild0_c004 + 0 + 0 + 0 = alpha parentChild0_c004 + 0 + 0 + 0 at h004
  change 0 + 0 + 0 + rho parentChild0_c112 = 0 + 0 + 0 + alpha parentChild0_c112 at h112
  change 0 + 0 + rho parentChild0_c103 + rho parentChild0_c112 = 0 + 0 + alpha parentChild0_c103 + alpha parentChild0_c112 at h103
  change 0 + rho parentChild0_c013 + 0 + rho parentChild0_c112 = 0 + alpha parentChild0_c013 + 0 + alpha parentChild0_c112 at h013
  simp only [zero_add, add_zero] at h004 h112 h103 h013
  funext c
  have hc : c ∈ ({parentChild0_c004, parentChild0_c013, parentChild0_c103, parentChild0_c112} : Finset parentChild0_Split116) := by
    rw [← parentChild0_split_univ]
    exact Finset.mem_univ c
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> linarith

/-- Every probability distribution on the splits of (1,1,6) has zero
maximum-entropy penalty because its coordinate marginals fix it uniquely. -/
private theorem parentChild0_mme_116_split_entropy_penalty_zero (alpha : Split 4 ![1, 1, 6] → ℝ)
    (hnonneg : ∀ c, 0 ≤ alpha c) (hmass : ∑ c, alpha c = 1) :
    entropyPenalty alpha = 0 := by
  have hset : SameMarginalDistributions alpha = {alpha} := by
    ext rho
    constructor
    · intro h
      exact Set.mem_singleton_iff.mpr (parentChild0_mme_116_split_marginals_injective alpha rho h.2.2)
    · rintro rfl
      exact ⟨hnonneg, hmass, fun _ _ => rfl⟩
  simp [entropyPenalty, hset]


open scoped Classical

/-- The maximum-entropy penalty vanishes in each of the six released regions. -/
private theorem parentChild0_mme_released_116_regional_entropy_penalty_zero (r : Fin 6) :
    entropyPenalty (fun c : Released116.Split =>
      (Released116.splitCount r c : ℝ) / Released116.regionalSize r) = 0 := by
  apply parentChild0_mme_116_split_entropy_penalty_zero
  · intro c
    positivity
  · have hm := (mme_released_116_regional_split_mass r).2
    change (∑ c : Split 4 ![1, 1, 6], Released116.splitCount r c) = _ at hm
    rw [← Finset.sum_div, ← Nat.cast_sum, hm]
    exact div_self (by exact_mod_cast (mme_released_116_regional_split_mass r).1.ne')

/-- The released (1,1,6) regional rate has no aggregate entropy-penalty term. -/
private theorem parentChild0_mme_released_116_penalty_potential_zero :
    RegionRate.penaltyPotential Released116.regionalSize Released116.splitCount = 0 := by
  simp [RegionRate.penaltyPotential, parentChild0_mme_released_116_regional_entropy_penalty_zero]


end PenaltyBound

open BigOperators MME MME.RegionRate
set_option autoImplicit false

/-- The released (1,1,6) regional rate is at least 0.2 per parent occurrence.
This combines certified entropy bounds for all three coordinates, including
both compatibility subtractions and the vanishing split entropy penalty. -/
private theorem parentChild0_mme_released_116_regional_rate_lower :
    (1 / 5 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      regionalRate Released116.parent_total Released116.regionalSize
        Released116.splitCount Released116.integerProfile := by
  have hx : (69 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      coarsePotential (half := 4) (parent := Released116.parent) Released116.splitCount 0 :=
    CoarseBound.parentChild0_mme_released_116_coarse_rate_lower
  have hy := ParentBound.parentChild0_mme_released_116_parent_y_entropy_lower
  have hz := ParentBound.parentChild0_mme_released_116_parent_z_entropy_lower
  have hcy := CompatibilityBound.parentChild0_mme_released_116_compatibility_y_entropy_upper
  have hcz := CompatibilityBound.parentChild0_mme_released_116_compatibility_z_entropy_upper
  have hn : (0 : ℝ) ≤ ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hl : Real.log 2 ≤ (7 / 10 : ℝ) := le_of_lt (Real.log_two_lt_d9.trans (by norm_num))
  have hnl := mul_le_mul_of_nonneg_left hl hn
  have hpen : penaltyPotential (half := 4) (parent := Released116.parent)
      Released116.regionalSize Released116.splitCount = 0 :=
    PenaltyBound.parentChild0_mme_released_116_penalty_potential_zero
  unfold regionalRate
  rw [hpen, sub_zero]
  refine le_min ?_ (le_min ?_ ?_) <;> nlinarith

/-- The exact released profile has a strictly positive regional entropy rate. -/
private theorem parentChild0_mme_released_116_regional_rate_positive :
    0 < regionalRate Released116.parent_total Released116.regionalSize
      Released116.splitCount Released116.integerProfile := by
  have hn : 0 < ∑ r : Fin 6, Released116.regionalSize r := by decide +kernel
  have hn' : (0 : ℝ) < ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) := by
    exact_mod_cast hn
  exact lt_of_lt_of_le (mul_pos (by norm_num) hn') parentChild0_mme_released_116_regional_rate_lower


/-- A fixed positive tolerance preserves a quantitative entropy margin for every
smaller nonnegative tolerance in the actual released profile. -/
private theorem parentChild0_mme_released_116_small_tolerance_rate_lower :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps₀ →
      (3 / 20 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
        regionalRate Released116.parent_total Released116.regionalSize
          Released116.splitCount Released116.integerProfile -
        ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteSplit.CompleteWord 2) eps := by
  obtain ⟨eps₀, heps₀, hmod⟩ :=
    (mme_regional_entropy_uniform_modulus (W := Fin 2 → CompleteSplit.CompleteWord 2)).2.2
      (1 / 20) (by norm_num)
  refine ⟨eps₀, heps₀, ?_⟩
  intro eps heps hsmall
  have h := mul_le_mul_of_nonneg_left (hmod eps heps hsmall)
    (Nat.cast_nonneg (α := ℝ) (∑ r : Fin 6, Released116.regionalSize r))
  have hr := parentChild0_mme_released_116_regional_rate_lower
  linarith


end RateBound

namespace AsymptoticBound

open scoped Classical
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

/-- Replicating every occurrence preserves each normalized child profile. -/
private theorem parentChild0_mme_cell_frequency_scale
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [cellFrequency, ← Finset.mul_sum, Nat.cast_mul]
  exact mul_div_mul_left _ _ hk'

/-- Uniform replication preserves the regional parent-mixture centers. -/
private theorem parentChild0_mme_parent_mixture_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (k : ℕ) (hk : 0 < k) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c v => k * mu c v) r w = parentMixture htotal n m mu r w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [parentMixture, parentChild0_mme_cell_frequency_scale mu k hk, Nat.cast_mul,
    mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hk'


open MME.RegionRate

private theorem parentChild0_mass_entropy_scale {W : Type*} [Fintype W] (k : ℕ) (x : W → ℕ) :
    massEntropy (fun w => ((k * x w : ℕ) : ℝ)) =
      (k : ℝ) * massEntropy (fun w => (x w : ℝ)) := by
  simpa only [Nat.cast_mul] using
    (mme_regional_mass_entropy_algebra (C := Unit) (W := W)).1 (k : ℝ)
      (fun w => (x w : ℝ))

private theorem parentChild0_potential_scale {C W : Type*} [Fintype C] [Fintype W]
    (k : ℕ) (mu : C → W → ℕ) :
    potential (fun c w => k * mu c w) = (k : ℝ) * potential mu := by
  rw [(mme_regional_mass_entropy_algebra (C := C) (W := W)).2.2,
    (mme_regional_mass_entropy_algebra (C := C) (W := W)).2.2,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => parentChild0_mass_entropy_scale k (mu c))

private theorem parentChild0_part_count_scale {C W G : Type*} [Fintype C]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ)
    (k : ℕ) (s : {c : C // boundary c} ⊕ G) (w : W) :
    partCount boundary group (fun c w => k * mu c w) s w =
      k * partCount boundary group mu s w := by
  classical
  cases s with
  | inl c => rfl
  | inr g => simp [partCount, Finset.mul_sum, mul_ite]

/-- Replicating the regional split counts multiplies their joint entropy
by the replication factor, including profiles with zero counts. -/
private theorem parentChild0_mme_regional_joint_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (k : ℕ) :
    jointPotential (fun r c => k * m r c) = (k : ℝ) * jointPotential m := by
  simp only [jointPotential, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => parentChild0_mass_entropy_scale k (m r))

private theorem parentChild0_coarse_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (k : ℕ) (i : Fin 3) :
    coarsePotential (fun r c => k * m r c) i = (k : ℝ) * coarsePotential m i := by
  simp only [coarsePotential, marginalCounts, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => parentChild0_mass_entropy_scale k _)

private theorem parentChild0_penalty_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (k : ℕ) (hk : 0 < k) :
    penaltyPotential (fun r => k * n r) (fun r c => k * m r c) =
      (k : ℝ) * penaltyPotential n m := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [penaltyPotential, Nat.cast_mul, mul_div_mul_left _ _ hk',
    mul_assoc, Finset.mul_sum]

private theorem parentChild0_parent_potential_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (k : ℕ) (hk : 0 < k) :
    parentPotential htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c w => k * mu c w) = (k : ℝ) * parentPotential htotal n m mu := by
  have heq (r : Fin R) :
      parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
        (fun c w => k * mu c w) r = parentMixture htotal n m mu r := by
    funext w
    exact parentChild0_mme_parent_mixture_scale htotal n m mu k hk r w
  simp only [parentPotential, heq, Nat.cast_mul, mul_assoc, Finset.mul_sum]

private theorem parentChild0_compatibility_potential_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ} (i : Fin 2)
    (mu : Cell half R parent → W → ℕ) (k : ℕ) :
    compatibilityPotential i (fun c w => k * mu c w) =
      (k : ℝ) * compatibilityPotential i mu := by
  simp only [compatibilityPotential]
  have heq : partCount (yzBoundary i) (modeGroup (yzMode i)) (fun c w => k * mu c w) =
      fun s w => k * partCount (yzBoundary i) (modeGroup (yzMode i)) mu s w := by
    funext s w
    exact parentChild0_part_count_scale _ _ _ _ _ _
  rw [heq, parentChild0_potential_scale]

/-- Uniform replication scales the minimum of the three summed regional
rates exactly; normalized parent profiles and entropy penalties are unchanged. -/
private theorem parentChild0_mme_regional_rate_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → W → ℕ) (k : ℕ) (hk : 0 < k) :
    regionalRate htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun i c w => k * mu i c w) = (k : ℝ) * regionalRate htotal n m mu := by
  simp only [regionalRate, parentChild0_coarse_potential_scale, parentChild0_penalty_potential_scale n m k hk,
    parentChild0_parent_potential_scale htotal n m _ k hk, parentChild0_compatibility_potential_scale,
    ← mul_sub, mul_min_of_nonneg _ _ (Nat.cast_nonneg k)]

/-- The entropy exponent controlling the hash scale is linear under uniform
replication, with the tolerance fixed before choosing the replication factor. -/
private theorem parentChild0_mme_regional_scale_exponent_scale {half R ell : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (eps : ℝ) (k : ℕ) (hk : 0 < k) :
    scaleExponent htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun i c w => k * mu i c w) eps =
        (k : ℝ) * scaleExponent htotal n m mu eps := by
  rw [scaleExponent, scaleExponent, parentChild0_mme_regional_joint_potential_scale,
    parentChild0_mme_regional_rate_scale htotal n m mu k hk]
  simp only [← Finset.mul_sum, Nat.cast_mul]
  ring


open BigOperators MME MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

private theorem parentChild0_replicated_size_le {R : ℕ} (n : Fin R → ℕ) (k : ℕ) :
    (((∑ r, k * n r : ℕ) : ℝ) + 1) ≤
      ((k : ℝ) + 1) * (((∑ r, n r : ℕ) : ℝ) + 1) := by
  rw [← Finset.mul_sum, Nat.cast_mul]
  nlinarith [(Nat.cast_nonneg (∑ r, n r) : (0 : ℝ) ≤ _), (Nat.cast_nonneg k : (0 : ℝ) ≤ _)]

private theorem parentChild0_polynomial_factor_scale_le {R : ℕ}
    (n : Fin R → ℕ) (k degree : ℕ) :
    polynomialFactor (fun r => k * n r) degree ≤
      ((k : ℝ) + 1) ^ degree * polynomialFactor n degree := by
  unfold polynomialFactor
  calc
    _ ≤ (((k : ℝ) + 1) * (6 * (((∑ r, n r : ℕ) : ℝ) + 1))) ^ degree := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [parentChild0_replicated_size_le n k]
    _ = _ := mul_pow _ _ _

private theorem parentChild0_ambient_factor_scale_le {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (k : ℕ) :
    ambientFactor (half := half) (parent := parent) (fun r => k * n r) ≤
      ((k : ℝ) + 1) ^ Fintype.card (Cell half R parent) *
        ambientFactor (half := half) (parent := parent) n := by
  unfold ambientFactor
  calc
    _ ≤ (((k : ℝ) + 1) * (((∑ r, n r : ℕ) : ℝ) + 1)) ^
        Fintype.card (Cell half R parent) := by
      gcongr
      exact parentChild0_replicated_size_le n k
    _ = _ := mul_pow _ _ _

/-- With the repair scale and profile types fixed, the prefactor in the
hash-scale estimate grows polynomially under replication of the parent sizes. -/
private theorem parentChild0_mme_regional_scale_factor_polynomial_replication
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell k : ℕ) :
    let degree := max (Fintype.card (Cell half R parent) + R * (half + 1))
      (R * (half + 1) + R * (half + 1) *
        Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell))
    scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell ≤
      ((k : ℝ) + 1) ^ degree *
        scaleFactor (half := half) (parent := parent) n d ell := by
  dsimp only
  let c := Fintype.card (Cell half R parent)
  let a := R * (half + 1)
  let b := a * Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell)
  let t : ℝ := k + 1
  have ht : 1 ≤ t := by dsimp [t]; exact le_add_of_nonneg_left (Nat.cast_nonneg k)
  have ht1 : 1 ≤ t ^ max (c + a) (a + b) := one_le_pow₀ ht
  have hca : t ^ (c + a) ≤ t ^ max (c + a) (a + b) :=
    pow_le_pow_right₀ ht (le_max_left _ _)
  have hab : t ^ (a + b) ≤ t ^ max (c + a) (a + b) :=
    pow_le_pow_right₀ ht (le_max_right _ _)
  have hfirst : ambientFactor (half := half) (parent := parent) (fun r => k * n r) *
      polynomialFactor (fun r => k * n r) a ≤
      t ^ max (c + a) (a + b) *
        (ambientFactor (half := half) (parent := parent) n * polynomialFactor n a) := by
    calc
      _ ≤ (t ^ c * ambientFactor (half := half) (parent := parent) n) *
          (t ^ a * polynomialFactor n a) := by
        apply mul_le_mul (parentChild0_ambient_factor_scale_le n k) (parentChild0_polynomial_factor_scale_le n k a)
        · unfold polynomialFactor; positivity
        · unfold ambientFactor; positivity
      _ = t ^ (c + a) *
          (ambientFactor (half := half) (parent := parent) n * polynomialFactor n a) := by
        rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hca (by
        unfold ambientFactor polynomialFactor; positivity)
  have hsecond : polynomialFactor (fun r => k * n r) a *
      polynomialFactor (fun r => k * n r) b ≤
      t ^ max (c + a) (a + b) * (polynomialFactor n a * polynomialFactor n b) := by
    calc
      _ ≤ (t ^ a * polynomialFactor n a) * (t ^ b * polynomialFactor n b) := by
        apply mul_le_mul (parentChild0_polynomial_factor_scale_le n k a) (parentChild0_polynomial_factor_scale_le n k b)
        · unfold polynomialFactor; positivity
        · unfold polynomialFactor; positivity
      _ = t ^ (a + b) * (polynomialFactor n a * polynomialFactor n b) := by
        rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hab (by unfold polynomialFactor; positivity)
  have hconst : (half : ℝ) + 2 ≤ t ^ max (c + a) (a + b) * ((half : ℝ) + 2) := by
    nlinarith [(Nat.cast_nonneg half : (0 : ℝ) ≤ _)]
  change (half : ℝ) + 2 + (8 * _ * _ + 128 * (d : ℝ) * _ * _) ≤ _
  dsimp only [scaleFactor, loadFactor]
  have hfirst' := mul_le_mul_of_nonneg_left hfirst (show (0 : ℝ) ≤ 8 by norm_num)
  have hsecond' := mul_le_mul_of_nonneg_left hsecond
    (show (0 : ℝ) ≤ 128 * (d : ℝ) by positivity)
  change (half : ℝ) + 2 + (8 * _ * _ + 128 * (d : ℝ) * _ * _) ≤
    t ^ max (c + a) (a + b) * ((half : ℝ) + 2 + (8 * _ * _ + 128 * (d : ℝ) * _ * _))
  nlinarith

open Filter

private theorem parentChild0_scale_factor_one_le {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) :
    1 ≤ scaleFactor (half := half) (parent := parent) n d ell := by
  have hload : 0 ≤ loadFactor (half := half) (parent := parent) n d ell := by
    unfold loadFactor ambientFactor polynomialFactor
    positivity
  unfold scaleFactor
  linarith [Nat.cast_nonneg (α := ℝ) half]

/-- The explicit polynomial prefactor contributes zero logarithmic cost per
replicated block in the limit, for any fixed repair scale and profile types. -/
private theorem parentChild0_mme_regional_scale_factor_log_div_tendsto_zero
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) :
    Tendsto (fun k : ℕ =>
      Real.log (scaleFactor (half := half) (parent := parent)
        (fun r => k * n r) d ell) / (k : ℝ)) atTop (nhds 0) := by
  let degree := max (Fintype.card (Cell half R parent) + R * (half + 1))
    (R * (half + 1) + R * (half + 1) *
      Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell))
  let C := scaleFactor (half := half) (parent := parent) n d ell
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (parentChild0_scale_factor_one_le n d ell)
  have hlog (k : ℕ) :
      Real.log (scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell) ≤
        (degree : ℝ) * Real.log ((k : ℝ) + 1) + Real.log C := by
    have hpos : 0 < scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell :=
      lt_of_lt_of_le zero_lt_one (parentChild0_scale_factor_one_le _ d ell)
    have h := Real.log_le_log hpos (parentChild0_mme_regional_scale_factor_polynomial_replication n d ell k)
    rw [Real.log_mul (pow_ne_zero _ (by positivity)) hC.ne', Real.log_pow] at h
    exact h
  have hloglim : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / (k : ℝ)) atTop (nhds 0) := by
    have ht : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp ht
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun k : ℕ =>
      ((degree : ℝ) * Real.log ((k : ℝ) + 1) + Real.log C) / (k : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero, add_div, mul_div_assoc, div_eq_mul_inv, add_mul, mul_assoc] using
      (hloglim.const_mul (degree : ℝ)).add (hinv.const_mul (Real.log C))
  apply squeeze_zero (fun k => div_nonneg
    (Real.log_nonneg (parentChild0_scale_factor_one_le _ d ell)) (Nat.cast_nonneg k))
    (fun k => div_le_div_of_nonneg_right (hlog k) (Nat.cast_nonneg k)) hupper


private theorem parentChild0_polynomial_factor_log_div_tendsto_zero {R : ℕ}
    (n : Fin R → ℕ) (degree : ℕ) :
    Tendsto (fun k : ℕ => Real.log (polynomialFactor (fun r => k * n r) degree) /
      (k : ℝ)) atTop (nhds 0) := by
  have hpos (m : Fin R → ℕ) : 0 < polynomialFactor m degree := by
    unfold polynomialFactor
    positivity
  have hone (m : Fin R → ℕ) : 1 ≤ polynomialFactor m degree := by
    apply one_le_pow₀
    nlinarith [Nat.cast_nonneg (α := ℝ) (∑ r, m r)]
  have hlog (k : ℕ) :
      Real.log (polynomialFactor (fun r => k * n r) degree) ≤
        (degree : ℝ) * Real.log ((k : ℝ) + 1) + Real.log (polynomialFactor n degree) := by
    have h := Real.log_le_log (hpos _) (parentChild0_polynomial_factor_scale_le n k degree)
    rw [Real.log_mul (pow_ne_zero _ (by positivity)) (hpos n).ne', Real.log_pow] at h
    exact h
  have hloglim : Tendsto (fun k : ℕ => Real.log ((k : ℝ) + 1) / (k : ℝ)) atTop (nhds 0) := by
    have ht : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    simpa [Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp ht
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun k : ℕ =>
      ((degree : ℝ) * Real.log ((k : ℝ) + 1) + Real.log (polynomialFactor n degree)) /
        (k : ℝ)) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero, add_div, mul_div_assoc, div_eq_mul_inv, add_mul,
      mul_assoc] using
      (hloglim.const_mul (degree : ℝ)).add (hinv.const_mul (Real.log (polynomialFactor n degree)))
  exact squeeze_zero (fun k => div_nonneg (Real.log_nonneg (hone _)) (Nat.cast_nonneg k))
    (fun k => div_le_div_of_nonneg_right (hlog k) (Nat.cast_nonneg k)) hupper

private theorem parentChild0_sqrt_div_tendsto_zero_of_linear_rate (x : ℕ → ℝ) (rate : ℝ)
    (hx : Tendsto (fun k : ℕ => x k / (k : ℝ)) atTop (nhds rate)) :
    Tendsto (fun k : ℕ => Real.sqrt (x k) / (k : ℝ)) atTop (nhds 0) := by
  have hi : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun k : ℕ => x k / (k : ℝ)^2) atTop (nhds 0) := by
    simpa [div_eq_mul_inv, pow_two, mul_assoc] using hx.mul hi
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_div' _ (sq_nonneg _),
    Real.sqrt_sq (Nat.cast_nonneg _)] using h

/-- The explicit entropy lower-bound expression has the regional rate minus
its fixed-tolerance entropy loss as its asymptotic logarithmic rate. Polynomial
prefactors and the progression loss contribute zero per replicated block. -/
private theorem parentChild0_mme_regional_entropy_expression_log_rate
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (eps : ℝ) (d : ℕ) :
    let size := fun k r => k * n r
    let counts := fun k r c => k * m r c
    let profiles := fun k i c w => k * mu i c w
    let E := fun k => regionalRate htotal (size k) (counts k) (profiles k)
    let loss := fun k => ((∑ r, size k r : ℕ) : ℝ) *
      entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps
    let theta := fun k => scaleExponent htotal (size k) (counts k) (profiles k) eps
    let factor := fun k => scaleFactor (half := half) (parent := parent) (size k) d ell
    Tendsto (fun k : ℕ =>
      Real.log (Real.exp (E k - loss k - 4 * Real.sqrt (Real.log (factor k) + theta k)) /
        (32 * polynomialFactor (size k) (Fintype.card (Cell half R parent)) * factor k)) /
          (k : ℝ)) atTop
      (nhds (regionalRate htotal n m mu - ((∑ r, n r : ℕ) : ℝ) *
        entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps)) := by
  dsimp only
  let rate := regionalRate htotal n m mu
  let loss := ((∑ r, n r : ℕ) : ℝ) *
    entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps
  let theta := scaleExponent htotal n m mu eps
  let factor := fun k => scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell
  let poly := fun k => polynomialFactor (fun r => k * n r) (Fintype.card (Cell half R parent))
  have hfac := parentChild0_mme_regional_scale_factor_log_div_tendsto_zero (half := half) (parent := parent) n d ell
  have hpoly := parentChild0_polynomial_factor_log_div_tendsto_zero n (Fintype.card (Cell half R parent))
  have hi : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have htheta : Tendsto (fun k : ℕ =>
      (Real.log (factor k) + (k : ℝ) * theta) / (k : ℝ)) atTop (nhds theta) := by
    have h := hfac.add_const theta
    convert h.congr' ?_ using 1
    · simp
    · filter_upwards [eventually_gt_atTop 0] with k hk
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      dsimp [factor]
      field_simp
  have hsqrt := parentChild0_sqrt_div_tendsto_zero_of_linear_rate _ theta htheta
  have hmain := (((tendsto_const_nhds (x := rate - loss)).sub (hsqrt.const_mul 4)).sub
    (hi.const_mul (Real.log 32))).sub hpoly |>.sub hfac
  convert hmain.congr' ?_ using 1
  · simp [rate, loss]
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hfactor : 0 < factor k :=
      lt_of_lt_of_le zero_lt_one (parentChild0_scale_factor_one_le _ d ell)
    have hpol : 0 < poly k := by dsimp [poly, polynomialFactor]; positivity
    rw [Real.log_div (Real.exp_ne_zero _) (mul_ne_zero
      (mul_ne_zero (by norm_num) hpol.ne') hfactor.ne'), Real.log_exp,
      Real.log_mul (mul_ne_zero (by norm_num) hpol.ne') hfactor.ne',
      Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hpol.ne']
    rw [parentChild0_mme_regional_rate_scale htotal n m mu k hk,
      parentChild0_mme_regional_scale_exponent_scale htotal n m mu eps k hk]
    simp only [← Finset.mul_sum, Nat.cast_mul]
    dsimp only [rate, loss, theta, factor, poly] at *
    field_simp
    ring


end AsymptoticBound

namespace PhysicalBound
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

/-! Entropy bounds for the physical hash construction, independent of an IntegerStep. -/

private theorem parentChild0_mme_regional_physical_common_scale_entropy_bound {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (ref : Address half R parent n) (href : ref ∈ RecursiveXHash.target m) :
    0 ≤ scaleExponent htotal n m mu eps ∧
    (commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i))
        (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m) : ℝ) ≤
      scaleFactor (half := half) (parent := parent) n d ell *
        Real.exp (scaleExponent htotal n m mu eps) := by
  have h := mme_regional_physical_hash_load_entropy_bounds htotal n m mu d eps heps ref href
  let theta := scaleExponent htotal n m mu eps
  let L := loadFactor (half := half) (parent := parent) n d ell
  have hL : 0 ≤ L := by dsimp [L, loadFactor, polynomialFactor, ambientFactor]; positivity
  have he : 1 ≤ Real.exp theta := Real.one_le_exp_iff.mpr h.1
  have hs := mme_common_hash_scale_real_upper_bound half
    (loadNum htotal m d (fun i ↦ mu (yzMode i))
      (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m)
    (L * Real.exp theta) (mul_nonneg hL (Real.exp_pos _).le) h.2
  refine ⟨h.1, hs.trans ?_⟩
  change (half : ℝ) + 2 + L * Real.exp theta ≤ ((half : ℝ) + 2 + L) * Real.exp theta
  have hh := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ (half : ℝ) + 2 by positivity)
  nlinarith

private theorem parentChild0_mme_regional_physical_entropy_selected_bound {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (d : ℕ) (eps : ℝ) (heps : 0 ≤ eps)
    (ref : Address half R parent n) (href : ref ∈ RecursiveXHash.target m) :
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i))
        (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m)
    let factor := scaleFactor (half := half) (parent := parent) n d ell
    let theta := scaleExponent htotal n m mu eps
    Real.exp (regionalRate htotal n m mu - ((∑ r, n r : ℕ) : ℝ) *
        entropyModulus (Fin 2 → CompleteWord ell) eps -
        4 * Real.sqrt (Real.log factor + theta)) /
      (32 * polynomialFactor n (Fintype.card (Cell half R parent)) * factor) ≤
    ((RecursiveXHash.target (n := n) m).card : ℝ) *
      Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) := by
  dsimp only
  have hs := parentChild0_mme_regional_physical_common_scale_entropy_bound htotal n m mu d eps heps ref href
  have ht := (mme_regional_target_entropy_bounds m 0 ref href).2.1
  have hQ : 0 < commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i))
        (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m) := by
    unfold commonScale
    exact (Nat.succ_pos half).trans_le (le_max_left _ _)
  have hp : 0 < polynomialFactor n (Fintype.card (Cell half R parent)) := by
    unfold polynomialFactor
    positivity
  have hf : 0 < scaleFactor (half := half) (parent := parent) n d ell := by
    unfold scaleFactor loadFactor polynomialFactor ambientFactor
    positivity
  have h := mme_entropy_retention_lower_bound
    ((RecursiveXHash.target (n := n) m).card : ℝ) (commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i))
        (fun i _ ↦ parentTypical htotal n m (mu (yzMode i)) eps)) (loadDen m) : ℝ)
    (jointPotential m) (scaleFactor (half := half) (parent := parent) n d ell)
    (scaleExponent htotal n m mu eps)
    (polynomialFactor n (Fintype.card (Cell half R parent)))
    (Nat.cast_nonneg _) (by exact_mod_cast hQ) hf hp ht hs.2
  have he : jointPotential m - scaleExponent htotal n m mu eps =
      regionalRate htotal n m mu - ((∑ r, n r : ℕ) : ℝ) *
        entropyModulus (Fin 2 → CompleteWord ell) eps := by
    unfold scaleExponent
    ring
  rw [he] at h
  exact h


end PhysicalBound

namespace Extraction

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

/-- A partition of physical parent positions splits a full-word histogram
into the exact pair-word histograms of its regions. -/
private theorem parentChild0_mme_parent_histogram_sum_over_regions
    {P A W : Type} [Fintype P] {R : ℕ} {n : Fin R → ℕ}
    (positions : (Σ r, Fin (n r)) ≃ P) (f : P → A)
    (pair : A ≃ (Fin 2 → W)) (a : A) :
    Fintype.card {p : P // f p = a} =
      ∑ r, Fintype.card {t : Fin (n r) //
        ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h} := by
  classical
  have hinj : Function.Injective (fun p : (Σ r, {t : Fin (n r) //
      ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h}) =>
      (⟨p.1,p.2.val⟩ : Σ r, Fin (n r))) := by
    rintro ⟨r,t,ht⟩ ⟨s,u,hu⟩ heq
    cases heq
    rfl
  let e : (Σ r, {t : Fin (n r) //
      ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h}) ≃
      {p : P // f p = a} := {
    toFun := fun p => ⟨positions ⟨p.1,p.2.val⟩, pair.injective (funext p.2.property)⟩
    invFun := fun p => ⟨(positions.symm p.val).1,
      ⟨(positions.symm p.val).2, by
        intro h
        simp only [Sigma.eta, Equiv.apply_symm_apply, p.property]⟩⟩
    left_inv := by
      intro p
      apply hinj
      exact positions.symm_apply_apply ⟨p.1,p.2.val⟩
    right_inv := by intro p; apply Subtype.ext; exact positions.apply_symm_apply p.val }
  rw [← Fintype.card_congr e, Fintype.card_sigma]

/-- Regional parent windows imply the full-word histogram window around
the regional-size-weighted mean of their centers. -/
private theorem parentChild0_mme_regional_parent_windows_imply_global_histogram_window
    {P A W : Type} [Fintype P] [Fintype W]
    {half R T : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (positions : (Σ r, Fin (n r)) ≃ P) (f : P → A)
    (pair : A ≃ (Fin 2 → W)) (eps : ℝ)
    (hn : ∀ r, 0 < n r) (hT : ∑ r, n r = T) (hTpos : 0 < T)
    (htypical : parentTypical htotal n m mu eps
      (fun p => pair (f (positions ⟨p.1,p.2.1⟩)) p.2.2)) :
    ∀ a : A, |(Fintype.card {p : P // f p = a} : ℝ) / T -
      ∑ r, ((n r : ℝ) / T) * parentMixture htotal n m mu r (pair a)| ≤ eps := by
  classical
  intro a
  let H (r : Fin R) := Fintype.card {t : Fin (n r) //
    ∀ h, pair (f (positions ⟨r,t⟩)) h = pair a h}
  have hcount := parentChild0_mme_parent_histogram_sum_over_regions positions f pair a
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hnr (r : Fin R) : (0 : ℝ) < n r := by exact_mod_cast hn r
  have hlocal (r : Fin R) :
      |(H r : ℝ) / n r - parentMixture htotal n m mu r (pair a)| ≤ eps :=
    (htypical r (pair a)).le
  have hid : (Fintype.card {p : P // f p = a} : ℝ) / T -
      ∑ r, ((n r : ℝ) / T) * parentMixture htotal n m mu r (pair a) =
      ∑ r, ((n r : ℝ) / T) *
        ((H r : ℝ) / n r - parentMixture htotal n m mu r (pair a)) := by
    rw [hcount, Nat.cast_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [H]
    field_simp [(hnr r).ne']
  rw [hid]
  calc
    _ ≤ ∑ r, |((n r : ℝ) / T) *
        ((H r : ℝ) / n r - parentMixture htotal n m mu r (pair a))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, ((n r : ℝ) / T) * eps := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul, abs_of_pos (div_pos (hnr r) hTr)]
      exact mul_le_mul_of_nonneg_left (hlocal r) (div_pos (hnr r) hTr).le
    _ = eps := by
      rw [← Finset.sum_mul, ← Finset.sum_div, ← Nat.cast_sum, hT,
        div_self hTr.ne', one_mul]


/-- Replicating every occurrence preserves each normalized child profile. -/
private theorem parentChild0_mme_cell_frequency_scale
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [cellFrequency, ← Finset.mul_sum, Nat.cast_mul]
  exact mul_div_mul_left _ _ hk'

/-- Uniform replication preserves the regional parent-mixture centers. -/
private theorem parentChild0_mme_parent_mixture_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (k : ℕ) (hk : 0 < k) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c v => k * mu c v) r w = parentMixture htotal n m mu r w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [parentMixture, parentChild0_mme_cell_frequency_scale mu k hk, Nat.cast_mul,
    mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hk'


open MME.Released116 MME.MoreAsymmetryExactSeed MME.CompleteSplit

/-- At every positive integer scale, the six regional windows imply a
full-word histogram window centered at the same released distribution. -/
private theorem parentChild0_mme_released_116_scaled_partition_parent_window (k : ℕ) (hk : 0 < k) :
    ∃ positions : (Σ r : Fin 6, Fin (k * regionalSize r)) ≃
        Fin (k * denominator ^ 4),
      ∀ (i : Fin 3) (f : Fin (k * denominator ^ 4) → CompleteWord 3) (eps : ℝ),
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (fun p =>
            let v := (completeWordSplitEquiv 2 (by decide)) (f (positions ⟨p.1,p.2.1⟩))
            ![v.1,v.2] p.2.2) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) // f p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  have hT : (∑ r : Fin 6, k * regionalSize r) = k * denominator ^ 4 := by
    rw [← Finset.mul_sum, mme_released_116_regional_total]
  have hcard : Fintype.card (Σ r : Fin 6, Fin (k * regionalSize r)) =
      Fintype.card (Fin (k * denominator ^ 4)) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hT
  let positions := Fintype.equivOfCardEq hcard
  refine ⟨positions, ?_⟩
  intro i f eps htypical w
  let pair := (completeWordSplitEquiv 2 (by decide)).trans
    (finTwoArrowEquiv (CompleteWord 2)).symm
  have h := parentChild0_mme_regional_parent_windows_imply_global_histogram_window
    parent_total (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w)
    positions f pair eps
    (fun r => Nat.mul_pos hk (mme_released_116_regional_split_mass r).1)
    hT (Nat.mul_pos hk (by norm_num [denominator])) htypical w
  have hpair (v : CompleteWord 3) : pair v =
      ![((completeWordSplitEquiv 2 (by decide)) v).1,
        ((completeWordSplitEquiv 2 (by decide)) v).2] := rfl
  have hweight (r : Fin 6) :
      ((k * regionalSize r : ℕ) : ℝ) / (k * denominator ^ 4 : ℕ) =
        (regionalSize r : ℝ) / (denominator : ℝ) ^ 4 := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [Nat.cast_mul, Nat.cast_pow]
    exact mul_div_mul_left _ _ hk'
  simp only [parentChild0_mme_parent_mixture_scale _ _ _ _ k hk, hweight, hpair] at h
  rw [mme_released_116_weighted_parent_center i w] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h


/-- A partition of parent words induces a child-position order that agrees
with literal left/right splitting of the same fine word. -/
private theorem parentChild0_mme_regional_parent_partition_fine_coordinates
    {R T : ℕ} {n : Fin R → ℕ}
    (positions : (Σ r, Fin (n r)) ≃ Fin T) :
    ∃ childPositions : Fin (T * 2) ≃ Position n,
      ∀ (x : ProfiledCW.FineWord (T * 4)) (p : Position n),
        ProfiledCW.split childPositions (show (T * 2) * 2 ^ (2 - 1) = T * 4 by omega) x p =
          (let v := completeWordSplitEquiv 2 (by decide)
            (ProfiledCW.split (Equiv.refl (Fin T)) rfl x (positions ⟨p.1,p.2.1⟩))
          ![v.1,v.2] p.2.2) := by
  let e : Fin (T * 2) ≃ Position n := finProdFinEquiv.symm.trans
    ((positions.symm.prodCongr (Equiv.refl (Fin 2))).trans
      (Equiv.sigmaProdDistrib (fun r => Fin (n r)) (Fin 2)))
  refine ⟨e, ?_⟩
  rintro x ⟨r,t,h⟩
  funext j
  fin_cases h <;> fin_cases j <;>
    simp [ProfiledCW.split, e, completeWordSplitEquiv, fineWordSplitEquiv,
      Equiv.sigmaProdDistrib, finProdFinEquiv, Nat.mul_add, ← Nat.mul_assoc, ← Nat.add_assoc]


/-- The scaled released histogram inclusion holds directly for the fine-word
splitting map required by an integer extraction step. -/
private theorem parentChild0_mme_released_116_scaled_fine_word_window (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * regionalSize r),
      ∀ (i : Fin 3) (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 by omega) x) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  obtain ⟨positions, hwindow⟩ := parentChild0_mme_released_116_scaled_partition_parent_window k hk
  obtain ⟨childPositions, hsplit⟩ := parentChild0_mme_regional_parent_partition_fine_coordinates positions
  refine ⟨childPositions, ?_⟩
  intro i x eps htypical w
  have hfun := funext (hsplit x)
  rw [hfun] at htypical
  exact hwindow i (ProfiledCW.split (Equiv.refl _) rfl x) eps htypical w

private theorem parentChild0_mme_child_grading_implies_parent_grading
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n) (f : Position n → CompleteWord ell)
    (hf : Graded htotal i a f) (r : Fin R) (t : Fin (n r)) :
    (∑ h : Fin 2, ∑ q, (f ⟨r,t,h⟩ q).val) = parent r i := by
  rw [Fin.sum_univ_two, hf, hf]
  simp only [fullCell, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  change ((a r t).val i).val + (parent r i - ((a r t).val i).val) = parent r i
  exact Nat.add_sub_of_le ((a r t).property.2 i)


private theorem parentChild0_grade_split_three (w : CompleteWord 3) :
    (∑ q, (w q).val) = ∑ h : Fin 2, ∑ q,
      ((![(completeWordSplitEquiv 2 (by decide) w).1,
        (completeWordSplitEquiv 2 (by decide) w).2] h) q).val := by
  simp [Fin.sum_univ_succ, completeWordSplitEquiv, fineWordSplitEquiv]
  omega

/-- The released histogram window and exact parent grades hold for the same
physical fine word whenever its child words are graded and parent typical. -/
private theorem parentChild0_mme_released_116_scaled_graded_fine_word_window (k : ℕ) (hk : 0 < k) :
    ∃ childPositions : Fin ((k * denominator ^ 4) * 2) ≃
        Position (fun r : Fin 6 => k * regionalSize r),
      ∀ (i : Fin 3) (a : Address 4 6 parent (fun r => k * regionalSize r))
        (x : ProfiledCW.FineWord ((k * denominator ^ 4) * 4)) (eps : ℝ),
        Graded parent_total i a (ProfiledCW.split childPositions
          (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
            (k * denominator ^ 4) * 4 by omega) x) →
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (ProfiledCW.split childPositions
            (show ((k * denominator ^ 4) * 2) * 2 ^ (2 - 1) =
              (k * denominator ^ 4) * 4 by omega) x) →
        (∀ p : Fin (k * denominator ^ 4),
          (∑ q, (ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p q).val)
            = parent 0 i) ∧
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) //
              ProfiledCW.split (ell := 3) (Equiv.refl (Fin (k * denominator ^ 4))) rfl x p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by
  classical
  obtain ⟨positions, hwindow⟩ := parentChild0_mme_released_116_scaled_partition_parent_window k hk
  obtain ⟨childPositions, hsplit⟩ := parentChild0_mme_regional_parent_partition_fine_coordinates positions
  refine ⟨childPositions, ?_⟩
  intro i a x eps hg ht
  constructor
  · intro p
    obtain ⟨⟨r,t⟩, rfl⟩ := positions.surjective p
    have h := parentChild0_mme_child_grading_implies_parent_grading parent_total i a _ hg r t
    simp only [hsplit] at h
    rw [parentChild0_grade_split_three]
    exact h
  · have hfun := funext (hsplit x)
    rw [hfun] at ht
    exact hwindow i (ProfiledCW.split (Equiv.refl _) rfl x) eps ht



open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false

private theorem parentChild0_mme_exact_step_source_refinement_on_unbroken
    {ell N : ℕ} {P Q : Predicate N} (E : ExactStep ell N P)
    (hPQ : ∀ j i f, f ∈ unbrokenWords E.stage.total i (E.address j) (E.stage.mu i) →
      P i (flatten E.stage.positions E.length f) →
      Q i (flatten E.stage.positions E.length f)) :
    ∃ F : ExactStep ell N Q, F.count = E.count ∧
      F.stage.repairExponent = E.stage.repairExponent ∧
      F.copies = E.copies ∧ F.output = E.output := by
  classical
  let F : ExactStep ell N Q := {
    hash := E.hash
    stage := E.stage
    level := E.level
    length := E.length
    count := E.count
    state := E.state
    address := E.address
    injective := E.injective
    target := E.target
    bucketed := E.bucketed
    hashed := E.hashed
    isolated := E.isolated
    holes := by
      intro j i
      apply le_trans _ (E.holes j i)
      apply Nat.mul_le_mul_left
      apply Finset.card_le_card
      apply Finset.union_subset_union
      · intro f hf
        obtain ⟨hf, hnot⟩ := Finset.mem_filter.mp hf
        exact Finset.mem_filter.mpr ⟨hf, fun hp => hnot (hPQ j i f hf hp)⟩
      · exact Finset.Subset.refl _ }
  exact ⟨F,rfl,rfl,rfl,rfl⟩

private theorem parentChild0_split_flatten {S : Type} {ell L M : ℕ} (positions : Fin L ≃ S)
    (length : L * 2 ^ (ell - 1) = M) (f : S → CompleteSplit.CompleteWord ell) :
    ProfiledCW.split positions length (ProfiledCW.flatten positions length f) = f := by
  funext p h
  simp [ProfiledCW.split, ProfiledCW.flatten]

private theorem parentChild0_mme_recursive_region_graded_source_exact_step_realization {half R ell N L M : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = M)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (hsupport : ∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val)
    (hboundary : BoundaryProfiles mu)
    (reference : Address half R parent n) (href : reference ∈ RecursiveXHash.target m)
    (k d : ℕ) (hk : 0 < k) (hd : 1 < d) (hkn : ∀ r, k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (k : ℝ) * eps ^ 2)
    (source : Predicate M)
    (hsource : ∀ i (a : Address half R parent n), a ∈ RecursiveXHash.target m →
      ∀ f : Position n → CompleteSplit.CompleteWord ell,
        Graded htotal i a f → parentTypical htotal n m (mu i) eps f →
        source i (ProfiledCW.flatten positions length f)) :
    let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
    let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
    ∃ E : ExactStep ell M source,
      ((RecursiveXHash.target (n := n) m).card : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
      E.stage.repairExponent = Nat.log d cap + 1 ∧
      E.output = fun i x ↦ Graded htotal i reference (ProfiledCW.split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (ProfiledCW.split positions length x) := by
  classical
  let P : Predicate M := fun i x ↦ parentTypical htotal n m (mu i) eps (ProfiledCW.split positions length x)
  let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
  let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
  let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
  have htype (i : Fin 3) (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m) :
      8 * d * (typeHoles htotal i a (mu i) (parentTypical htotal n m (mu i) eps)).card ≤
        (unbrokenWords htotal i a (mu i)).card :=
    mme_recursive_region_derived_parent_hole_budget parent n htotal m (mu i) (hmass i) i (hsupport i)
      k d hk hkn hdiv eps heps hscale a ha
  obtain ⟨p,hprime,hodd,hgrade,hlow,hupp,S,hSr,hSf,state,I,hIt,hIb,hIh,hIu,hIso,hIc⟩ :=
    mme_recursive_region_computed_hash_selection parent n htotal m e d (fun i ↦ mu (yzMode i))
      (fun i ↦ hmass (yzMode i)) keep (fun i a ha ↦ htype (yzMode i) a ha)
  let D : HashExtraction.HashData := {
    half := half
    R := R
    parent := parent
    n := n
    m := m
    N := N
    p := p
    prime := hprime
    odd := hodd
    grade_lt := hgrade
    positions := e
    labels := S
    labels_range := hSr
    labels_free := hSf
    good := fun state ↦ usable htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state d
      (fun i ↦ mu (yzMode i)) keep }
  let A : Stage D := {
    ell := ell
    L := L
    repairScale := d
    repairExponent := Nat.log d cap + 1
    total := htotal
    half_eq := hhalf
    positions := positions
    mu := mu
    boundary := hboundary
    mass := hmass
    reference := reference
    reference_target := href
    keep := keep
    good_eq := fun _ ↦ rfl
    capacity := Nat.lt_pow_succ_log_self hd cap }
  let address (j : Fin I.card) : Address half R parent n := (I.equivFin.symm j).val
  have hj (j : Fin I.card) : address j ∈ I := (I.equivFin.symm j).property
  have haddr : Function.Injective address := Subtype.val_injective.comp I.equivFin.symm.injective
  have hsplit (i : Fin 3) (f : Position n → CompleteSplit.CompleteWord ell) :
      P i (ProfiledCW.flatten positions length f) = parentTypical htotal n m (mu i) eps f := by
    simp only [P, parentChild0_split_flatten]
  have hholes (j : Fin I.card) (i : Fin 3) :
      4 * d * (((unbrokenWords htotal i (address j) (mu i)).filter
          (fun f ↦ ¬ P i (ProfiledCW.flatten positions length f))) ∪
        (if i = 1 then filterHoles htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state 0 (mu 1) (address j) (keep 0 (address j))
         else if i = 2 then filterHoles htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state 1 (mu 2) (address j) (keep 1 (address j))
         else ∅)).card ≤ (unbrokenWords htotal i (address j) (mu i)).card := by
    have hu : ∀ i : Fin 2,
        4 * d * (filterHoles htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state i
          (mu (yzMode i)) (address j) (keep i (address j))).card ≤
            (unbrokenWords htotal (yzMode i) (address j) (mu (yzMode i))).card :=
      (Finset.mem_filter.mp (hIu (hj j))).2
    fin_cases i
    · have hh := htype 0 (address j) (hIt (hj j))
      have hsmall : 4 * d * (typeHoles htotal 0 (address j) (mu 0) (parentTypical htotal n m (mu 0) eps)).card ≤
          (unbrokenWords htotal 0 (address j) (mu 0)).card :=
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right d (by decide : 4 ≤ 8))).trans hh
      simpa [hsplit, typeHoles] using hsmall
    · simpa [hsplit, keep, yzMode, filterHoles, typeHoles, ← Finset.union_assoc] using hu 0
    · simpa [hsplit, keep, yzMode, filterHoles, typeHoles, ← Finset.union_assoc] using hu 1
  let E : ExactStep ell M P := {
    hash := D
    stage := A
    level := rfl
    length := length
    count := I.card
    state := state
    address := address
    injective := haddr
    target := fun j ↦ hIt (hj j)
    bucketed := fun j ↦ hIb (hj j)
    hashed := fun j ↦ hIh (hj j)
    isolated := fun j b hb he ↦ hIso (address j) (hj j) b hb he
    holes := hholes }
  have hincl : ∀ j i f,
      f ∈ unbrokenWords E.stage.total i (E.address j) (E.stage.mu i) →
      P i (ProfiledCW.flatten E.stage.positions E.length f) →
      source i (ProfiledCW.flatten E.stage.positions E.length f) := by
    intro j i f hf hp
    apply hsource i (address j) (hIt (hj j)) f
    · exact (Finset.mem_filter.mp hf).2.1
    · exact (hsplit i f).mp hp
  obtain ⟨F, hcount, hexponent, _, houtput⟩ :=
    parentChild0_mme_exact_step_source_refinement_on_unbroken E hincl
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [hcount] using hIc
  · exact hexponent
  · exact houtput


open MME.ProfiledCW MME.RecursiveYZ.CWCells

/-- The concrete released integer profiles give an exact extraction from the
simultaneously graded global histogram window at every admissible scale. -/
private theorem parentChild0_mme_released_116_graded_histogram_exact_step_with_repair_scale
    (d : ℕ) (hd : 1 < d) (k : ℕ) (hk : 0 < k) (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * 6 * (Fintype.card (CompleteWord 2) : ℝ) ^ 2) ≤
      (k * denominator ^ 2 : ℕ) * eps ^ 2) :
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
        ((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell parent_total reference)
            (fun c i => (c.2.val i).val) mu i)) + 1 ∧
        E.output = fun i x => Graded parent_total i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell parent_total reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x) := by
  classical
  dsimp only
  obtain ⟨positions, hwindow⟩ := parentChild0_mme_released_116_scaled_graded_fine_word_window k hk
  obtain ⟨reference, href⟩ := mme_released_116_scaled_reference_exists k
  have hT : 0 < k * denominator ^ 4 := Nat.mul_pos hk (by norm_num [denominator])
  have hcard : Fintype.card (Σ r : Fin 6, Fin (k * regionalSize r)) =
      k * denominator ^ 4 := by
    simp only [Fintype.card_sigma, Fintype.card_fin, ← Finset.mul_sum,
      mme_released_116_regional_total]
  let e : Fin ((k * denominator ^ 4 - 1) + 1) ≃
      (Σ r : Fin 6, Fin (k * regionalSize r)) :=
    (finCongr (Nat.sub_add_cancel hT)).trans (Fintype.equivFinOfCardEq hcard).symm
  have hmass : ∀ i c, ∑ w, k * integerProfile i c w =
      k * splitCount c.1 c.2 + k * splitCount c.1 (complement (parent_total c.1) c.2) := by
    intro i c
    rw [← Finset.mul_sum, mme_released_116_integer_profile_mass, Nat.mul_add]
  have hsupport : ∀ i c w, 0 < k * integerProfile i c w →
      ∑ h, (w h).val = (c.2.val i).val := by
    intro i c w hw
    exact mme_released_116_integer_profile_support i c w (Nat.pos_of_mul_pos_left hw)
  have hboundary : BoundaryProfiles (fun i c w => k * integerProfile i c w) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c hc w
      exact congrArg (k * ·) (mme_released_116_integer_profile_boundary.1 c hc w)
    · intro c hc w
      exact congrArg (k * ·) (mme_released_116_integer_profile_boundary.2.1 c hc w)
    · intro c hc w
      exact congrArg (k * ·) (mme_released_116_integer_profile_boundary.2.2 c hc w)
  obtain ⟨hminimum, hsize, hdiv⟩ := mme_released_116_scaled_integer_divisibility k hk
  refine ⟨positions, reference, href, ?_⟩
  apply parentChild0_mme_recursive_region_graded_source_exact_step_realization parent
    (fun r => k * regionalSize r) parent_total (by decide)
    (fun r c => k * splitCount r c) e positions (by omega)
    (fun i c w => k * integerProfile i c w) hmass hsupport hboundary reference href
    (k * denominator ^ 2) d hminimum hd hsize hdiv eps heps hscale
  intro i a ha f hg ht
  have h := hwindow i a (ProfiledCW.flatten positions (by omega) f) eps
  rw [parentChild0_split_flatten] at h
  exact h hg ht

private theorem parentChild0_mme_released_116_arbitrarily_large_size_test
    (d : ℕ) (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧
      (8 * d : ℝ) * (25 * 6 *
        (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2) ≤
        (k * denominator ^ 2 : ℕ) * eps ^ 2 := by
  let B : ℝ := (8 * d : ℝ) * (25 * 6 *
    (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2)
  have hfactor : 0 < (denominator : ℝ) ^ 2 * eps ^ 2 := by
    exact mul_pos (by norm_num [denominator]) (sq_pos_of_pos heps)
  obtain ⟨j, hj⟩ := exists_nat_gt (B / ((denominator : ℝ) ^ 2 * eps ^ 2))
  let k := 2 * max K (j + 1)
  have hK : K ≤ k := by
    have := le_max_left K (j + 1)
    dsimp [k]
    omega
  have hjk : j < k := by
    have := le_max_right K (j + 1)
    dsimp [k]
    omega
  have heven : Even k := ⟨max K (j + 1), by dsimp [k]; omega⟩
  have hkr : (j : ℝ) < k := by exact_mod_cast hjk
  have hB : B < (k : ℝ) * ((denominator : ℝ) ^ 2 * eps ^ 2) :=
    (div_lt_iff₀ hfactor).mp (hj.trans hkr)
  refine ⟨k, hK, lt_of_le_of_lt (Nat.zero_le j) hjk, heven, ?_⟩
  simpa only [B, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hB.le

/-- Every positive tolerance admits arbitrarily large replicated released
profiles with a quantitative exact extraction from the graded histogram window. -/
private theorem parentChild0_mme_released_116_cofinal_graded_histogram_exact_step_with_repair_scale
    (d : ℕ) (hd : 1 < d) (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
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
        ((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell parent_total reference)
            (fun c i => (c.2.val i).val) mu i)) + 1 ∧
        E.output = fun i x => Graded parent_total i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell parent_total reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x) := by
  obtain ⟨k, hK, hk, heven, hscale⟩ := parentChild0_mme_released_116_arbitrarily_large_size_test d eps heps K
  exact ⟨k, hK, hk, heven, parentChild0_mme_released_116_graded_histogram_exact_step_with_repair_scale d hd k hk eps heps hscale⟩


open MME MME.ProfiledCW
set_option autoImplicit false

/-- Repair divides the selected count by its power-of-eight budget;
the integer rounding loses strictly less than one additional copy. -/
private theorem parentChild0_mme_exact_step_copies_gt_normalized_count_sub_one
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) {B : ℝ}
    (hB : B ≤ E.count) :
    B / (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies := by
  have hd : 0 < 8 ^ E.stage.repairExponent := pow_pos (by decide) _
  have hn : E.count < 8 ^ E.stage.repairExponent * (E.copies + 1) := by
    have hmod := Nat.mod_lt E.count hd
    have h := Nat.mod_add_div E.count (8 ^ E.stage.repairExponent)
    dsimp [ExactStep.copies]
    nlinarith
  have hr : (E.count : ℝ) < (8 : ℝ) ^ E.stage.repairExponent * ((E.copies : ℝ) + 1) := by
    exact_mod_cast hn
  have hdR : 0 < (8 : ℝ) ^ E.stage.repairExponent := pow_pos (by norm_num) _
  have h : B / (8 : ℝ) ^ E.stage.repairExponent < (E.copies : ℝ) + 1 :=
    (div_lt_iff₀ hdR).mpr (hB.trans_lt (by simpa only [mul_comm] using hr))
  linarith


/-- The actual tensor restriction retains the post-repair copy count,
with its quantitative lower bound including the integer-rounding loss. -/
private theorem parentChild0_mme_exact_step_quantitative_tensor_restriction
    {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (E : ExactStep ell N P) {B : ℝ} (hB : B ≤ E.count) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin E.copies => tensor K E.output)) (tensor K P) ∧
      B / (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies := by
  exact ⟨mme_recursive_profiled_CW_exact_step E,
    parentChild0_mme_exact_step_copies_gt_normalized_count_sub_one E hB⟩

/-- Cofinal released profiles give actual tensor restrictions over any field,
with all repair and integer-rounding losses retained in the copy bound. -/
private theorem parentChild0_mme_released_116_cofinal_graded_histogram_tensor_restriction
    {KField : Type u} [Field KField] (d : ℕ) (hd : 1 < d) (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
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
        ((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell parent_total reference)
            (fun c i => (c.2.val i).val) mu i)) + 1 ∧
        (E.output = fun i x => Graded parent_total i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell parent_total reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x) ) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin E.copies => tensor KField E.output))
          (tensor KField source) ∧
        (((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q)) /
          (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies := by
  classical
  dsimp only
  obtain ⟨k, hK, hk, heven, positions, reference, href, E, hcount, hexponent, houtput⟩ :=
    parentChild0_mme_released_116_cofinal_graded_histogram_exact_step_with_repair_scale d hd eps heps K
  exact ⟨k, hK, hk, heven, positions, reference, href, E, hcount, hexponent, houtput,
    parentChild0_mme_exact_step_quantitative_tensor_restriction E hcount⟩



set_option autoImplicit false

/-- The repair budget has logarithmic cost controlled by the capacity,
with the base-change factor exposed for choosing the repair scale. -/
private theorem parentChild0_mme_repair_budget_log_le (d C : ℕ) :
    Real.log ((8 : ℝ) ^ (Nat.log d C + 1)) ≤
      Real.log 8 + (Real.log 8 / Real.log d) * Real.log C := by
  have h := Real.natLog_le_logb C d
  have h8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hm := mul_le_mul_of_nonneg_right h h8
  rw [Real.log_pow]
  simp only [Real.logb, Nat.cast_add, Nat.cast_one] at hm ⊢
  convert add_le_add_right hm (Real.log 8) using 1 <;> ring

/-- One repair scale makes its logarithmic cost an arbitrarily small
fraction of log capacity, uniformly over every natural capacity. -/
private theorem parentChild0_mme_repair_scale_exists_uniform_log_loss (delta : ℝ) (hdelta : 0 < delta) :
    ∃ d : ℕ, 1 < d ∧ ∀ C : ℕ,
      Real.log ((8 : ℝ) ^ (Nat.log d C + 1)) ≤ Real.log 8 + delta * Real.log C := by
  obtain ⟨s, hs⟩ := exists_nat_gt (1 / delta)
  let d := 8 ^ (s + 1)
  have hd : 1 < d := by
    dsimp [d]
    rw [pow_succ]
    have hp : 0 < 8 ^ s := pow_pos (by decide) _
    omega
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hdR : (1 : ℝ) < d := by exact_mod_cast hd
  have hlogd : Real.log (d : ℝ) = ((s : ℝ) + 1) * Real.log 8 := by
    simp [d, Nat.cast_pow, Real.log_pow]
  have hs' : 1 < (s : ℝ) * delta := (div_lt_iff₀ hdelta).mp hs
  have hratio : Real.log 8 / Real.log d ≤ delta := by
    apply (div_le_iff₀ (Real.log_pos hdR)).mpr
    rw [hlogd]
    nlinarith
  refine ⟨d, hd, fun C => (parentChild0_mme_repair_budget_log_le d C).trans ?_⟩
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_right hratio (Real.log_natCast_nonneg C))


open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

/-- Every graded profile is a subset of the complete-word functions on its
positions, so three mode profiles have at most the unrestricted triple count. -/
private theorem parentChild0_mme_profile_capacity_le_unrestricted
    {P C : Type*} [Fintype P] (ell : ℕ) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) ≤
      3 ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
  have h (i : Fin 3) : Nat.card (Block ell cell shape mu i) ≤
      (3 ^ (2 ^ (ell - 1))) ^ Fintype.card P := by
    have h := Nat.card_le_card_of_injective
      (fun f : Block ell cell shape mu i => f.val) Subtype.val_injective
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin] using h
  calc
    _ ≤ ∏ _ : Fin 3, (3 ^ (2 ^ (ell - 1))) ^ Fintype.card P :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => h i)
    _ = _ := by simp [← pow_mul, Nat.mul_comm]

/-- The logarithm of the repair capacity is bounded linearly in the number
of fine-word coordinates, independently of the specific profiles. -/
private theorem parentChild0_mme_profile_capacity_log_le_fine_length
    {P C : Type*} [Fintype P] (ell : ℕ) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    Real.log (∏ i : Fin 3, Nat.card (Block ell cell shape mu i) : ℕ) ≤
      (3 * (Fintype.card P * 2 ^ (ell - 1)) : ℕ) * Real.log 3 := by
  let cap := ∏ i : Fin 3, Nat.card (Block ell cell shape mu i)
  by_cases hc : cap = 0
  · change Real.log (cap : ℝ) ≤ _
    rw [hc, Nat.cast_zero, Real.log_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  · have hpos : (0 : ℝ) < cap := by exact_mod_cast Nat.pos_of_ne_zero hc
    have hbound : (cap : ℝ) ≤ (3 : ℝ) ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
      exact_mod_cast parentChild0_mme_profile_capacity_le_unrestricted ell cell shape mu
    have h := Real.log_le_log hpos hbound
    rw [Real.log_pow] at h
    exact h


/-- One repair scale makes the logarithmic repair budget at most eta per
fine coordinate, up to the fixed log-eight overhead, for every profile. -/
private theorem parentChild0_mme_profile_repair_scale_exists_uniform_coordinate_loss
    (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℕ, 1 < d ∧ ∀ (ell : ℕ) (P C : Type*) [Fintype P]
      (cell : P → C) (shape : C → Fin 3 → ℕ)
      (mu : Fin 3 → C → CompleteWord ell → ℕ),
      Real.log ((8 : ℝ) ^ (Nat.log d
        (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) + 1)) ≤
        Real.log 8 + eta * (Fintype.card P * 2 ^ (ell - 1) : ℕ) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < 3 * Real.log 3 := mul_pos (by norm_num) h3
  obtain ⟨d, hd, hbudget⟩ := parentChild0_mme_repair_scale_exists_uniform_log_loss
    (eta / (3 * Real.log 3)) (div_pos heta hden)
  refine ⟨d, hd, ?_⟩
  intro ell P C inst cell shape mu
  have hcap := parentChild0_mme_profile_capacity_log_le_fine_length ell cell shape mu
  calc
    _ ≤ Real.log 8 + (eta / (3 * Real.log 3)) *
        Real.log (∏ i : Fin 3, Nat.card (Block ell cell shape mu i) : ℕ) := hbudget _
    _ ≤ Real.log 8 + (eta / (3 * Real.log 3)) *
        ((3 * (Fintype.card P * 2 ^ (ell - 1)) : ℕ) * Real.log 3) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hcap (div_pos heta hden).le)
    _ = _ := by
      push_cast
      field_simp


open MME.Released116 MME.MoreAsymmetryExactSeed

/-- The released six-region child positions occupy exactly four fine
coordinates per replicated parent position. -/
private theorem parentChild0_mme_released_116_scaled_fine_coordinate_card (k : ℕ) :
    Fintype.card (Position (fun r : Fin 6 => k * regionalSize r)) * 2 ^ (2 - 1) =
      4 * (k * denominator ^ 4) := by
  simp only [Position, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [← Finset.sum_mul, ← Finset.mul_sum, mme_released_116_regional_total]
  ring

/-- One repair scale controls every replicated released profile, uniformly
in the reference address, at eta per physical fine coordinate. -/
private theorem parentChild0_mme_released_116_uniform_repair_coordinate_loss (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℕ, 1 < d ∧ ∀ (k : ℕ)
      (reference : MME.RecursiveXHash.Address 4 6 parent
        (fun r => k * regionalSize r)),
      Real.log ((8 : ℝ) ^ (Nat.log d
        (∏ i : Fin 3, Nat.card (Block 2 (fullCell parent_total reference)
          (fun c i => (c.2.val i).val) (fun i c w => k * integerProfile i c w) i)) + 1)) ≤
        Real.log 8 + eta * (4 * (k * denominator ^ 4) : ℕ) := by
  obtain ⟨d, hd, hbudget⟩ := parentChild0_mme_profile_repair_scale_exists_uniform_coordinate_loss eta heta
  refine ⟨d, hd, ?_⟩
  intro k reference
  have h := hbudget 2 _ _ (fullCell parent_total reference)
    (fun c i => (c.2.val i).val) (fun i c w => k * integerProfile i c w)
  rw [parentChild0_mme_released_116_scaled_fine_coordinate_card] at h
  exact h


/-- A single repair scale gives cofinal actual released tensor restrictions
with arbitrarily small repair loss per fine coordinate. The scale is fixed
before choosing the replication lower bound. -/
private theorem parentChild0_mme_released_116_cofinal_tensor_restriction_uniform_repair_loss
    {KField : Type u} [Field KField] (eta : ℝ) (heta : 0 < eta) (eps : ℝ) (heps : 0 < eps) :
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
        ((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
        E.stage.repairExponent = Nat.log d
          (∏ i : Fin 3, Nat.card (Block 2 (fullCell parent_total reference)
            (fun c i => (c.2.val i).val) mu i)) + 1 ∧
        Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤
          Real.log 8 + eta * (4 * (k * denominator ^ 4) : ℕ) ∧
        (E.output = fun i x => Graded parent_total i reference
          (ProfiledCW.split (ell := 2) positions (by omega) x) ∧
          Useful (fullCell parent_total reference) (mu i)
            (ProfiledCW.split (ell := 2) positions (by omega) x) ) ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin E.copies => tensor KField E.output))
          (tensor KField source) ∧
        (((RecursiveXHash.target (n := n) m).card : ℝ) *
          Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q)) /
          (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies  := by
  classical
  obtain ⟨d, hd, hbudget⟩ := parentChild0_mme_released_116_uniform_repair_coordinate_loss eta heta
  refine ⟨d, hd, ?_⟩
  intro K
  dsimp only
  obtain ⟨k, hK, hk, heven, positions, reference, href, E, hcount, hexponent,
    houtput, hrestrict, hcopies⟩ :=
    parentChild0_mme_released_116_cofinal_graded_histogram_tensor_restriction
      (KField := KField) d hd eps heps K
  refine ⟨k, hK, hk, heven, positions, reference, href, E, hcount, hexponent, ?_,
    houtput, hrestrict, hcopies⟩
  rw [hexponent]
  exact hbudget k reference


end Extraction

namespace EventualBound
open Filter Topology
set_option autoImplicit false

/-- A strict gap between an asymptotic logarithmic rate and a linear repair
cost eventually pays any fixed overhead. -/
private theorem parentChild0_mme_eventually_log_exceeds_linear_cost (B : ℕ → ℝ) (rate cost overhead : ℝ)
    (hlim : Tendsto (fun k => Real.log (B k) / (k : ℝ)) atTop (nhds rate))
    (hgap : cost < rate) :
    ∀ᶠ k : ℕ in atTop, overhead + cost * (k : ℝ) < Real.log (B k) := by
  have hi : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun k => Real.log (B k) / (k : ℝ) - overhead / (k : ℝ))
      atTop (nhds rate) := by
    simpa only [div_eq_mul_inv, mul_zero, sub_zero] using hlim.sub (hi.const_mul overhead)
  have hev := h.eventually (lt_mem_nhds hgap)
  filter_upwards [hev, eventually_gt_atTop 0] with k hk hkpos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hdiv : cost < (Real.log (B k) - overhead) / (k : ℝ) := by
    simpa only [sub_div] using hk
  have hmul := (lt_div_iff₀ hkR).mp hdiv
  linarith


end EventualBound
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ
open MME.CompleteSplit MME.ProfiledCW MME.RecursiveYZ.CWCells
open MME.Released116 MME.MoreAsymmetryExactSeed
open scoped Classical
set_option autoImplicit false

private theorem parentChild0_survival_scale_factor_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) :
    0 < scaleFactor (half := half) (parent := parent) n d ell := by
  unfold scaleFactor loadFactor ambientFactor polynomialFactor
  positivity

private theorem parentChild0_survival_polynomial_factor_pos {R : ℕ} (n : Fin R → ℕ) (degree : ℕ) :
    0 < polynomialFactor n degree := by
  unfold polynomialFactor
  positivity

/-- At every sufficiently small positive tolerance, actual released tensor
restrictions exist at cofinally many even scales with positive surviving copies. -/
private theorem mme_released_116_cofinal_even_tensor_restriction_positive_copies
    {KField : Type u} [Field KField]  :
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
          (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies   := by
  classical
  obtain ⟨eps0, heps0, hrate⟩ := RateBound.parentChild0_mme_released_116_small_tolerance_rate_lower
  refine ⟨eps0, heps0, ?_⟩
  intro eps heps hepsle
  obtain ⟨d, hd, hcofinal⟩ :=
    Extraction.parentChild0_mme_released_116_cofinal_tensor_restriction_uniform_repair_loss
      (KField := KField) (1 / 80) (by norm_num) eps heps
  refine ⟨d, hd, ?_⟩
  let N : ℝ := (∑ r, regionalSize r : ℕ)
  let size := fun k r => k * regionalSize r
  let counts := fun k r c => k * splitCount r c
  let profiles := fun k i c w => k * integerProfile i c w
  let factor := fun k => scaleFactor (half := 4) (parent := parent) (size k) d 2
  let B := fun k => Real.exp
    (regionalRate parent_total (size k) (counts k) (profiles k) -
      ((∑ r, size k r : ℕ) : ℝ) * entropyModulus (Fin 2 → CompleteWord 2) eps -
      4 * Real.sqrt (Real.log (factor k) +
        scaleExponent parent_total (size k) (counts k) (profiles k) eps)) /
      (32 * polynomialFactor (size k) (Fintype.card (Cell 4 6 parent)) * factor k)
  have hlim := AsymptoticBound.parentChild0_mme_regional_entropy_expression_log_rate
    parent_total regionalSize splitCount integerProfile eps d
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (show 0 < ∑ r, regionalSize r by decide +kernel)
  have hgap : N / 20 < regionalRate parent_total regionalSize splitCount integerProfile -
      N * entropyModulus (Fin 2 → CompleteWord 2) eps := by
    have h := hrate eps heps.le hepsle
    change (3 / 20 : ℝ) * N ≤ _ at h
    linarith
  have hev := EventualBound.parentChild0_mme_eventually_log_exceeds_linear_cost B _ (N / 20)
    (Real.log 2 + Real.log 8) hlim hgap
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hev
  intro K
  obtain ⟨k, hK, hk, heven, positions, reference, href, E, hcount, hexponent,
    hrepair, houtput, hrestrict, hcopies⟩ := hcofinal (max K K0)
  refine ⟨k, (le_max_left K K0).trans hK, hk, heven, positions, reference, href,
    E, ?_, hcount, hexponent, hrepair, houtput, hrestrict, hcopies⟩
  have hselected := PhysicalBound.parentChild0_mme_regional_physical_entropy_selected_bound
    parent_total (size k) (counts k) (profiles k) d eps heps.le reference href
  have hf : 0 < factor k := by
    change 0 < scaleFactor (half := 4) (parent := parent) (size k) d 2
    exact parentChild0_survival_scale_factor_pos (size k) d 2
  have hp : 0 < polynomialFactor (size k) (Fintype.card (Cell 4 6 parent)) :=
    parentChild0_survival_polynomial_factor_pos _ _
  have hB : 0 < B k :=
    div_pos (Real.exp_pos _) (mul_pos (mul_pos (by norm_num) hp) hf)
  have hD : 0 < (8 : ℝ) ^ E.stage.repairExponent := pow_pos (by norm_num) _
  have hbudget : Real.log ((8 : ℝ) ^ E.stage.repairExponent) ≤
      Real.log 8 + N / 20 * (k : ℝ) := by
    convert hrepair using 1
    dsimp [N]
    rw [mme_released_116_regional_total]
    push_cast
    ring
  have hlog := hK0 k ((le_max_right K K0).trans hK)
  have hlarge : 2 * (8 : ℝ) ^ E.stage.repairExponent < B k := by
    apply (Real.log_lt_log_iff (mul_pos (by norm_num) hD) hB).mp
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hD.ne']
    linarith
  have htwo : 2 < B k / (8 : ℝ) ^ E.stage.repairExponent :=
    (lt_div_iff₀ hD).mpr hlarge
  change B k ≤ _ at hselected
  have hdiv := div_le_div_of_nonneg_right hselected hD.le
  have hnorm : B k / (8 : ℝ) ^ E.stage.repairExponent - 1 < (E.copies : ℝ) :=
    (sub_le_sub_right hdiv 1).trans_lt hcopies
  have hpos : (0 : ℝ) < E.copies := by linarith only [hnorm, htwo]
  exact_mod_cast hpos



open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
set_option autoImplicit false

private theorem parentChild1_profiled0_intact0_fullChild0_word_grade_zero {ell : ℕ} (s : CompleteWord ell)
    (h : CWCells.grade s = 0) : s = fun _ ↦ 0 := by
  funext r
  apply Fin.ext
  have hh : ∀ r, (s r).val = 0 := by
    simpa [CWCells.grade] using (Finset.sum_eq_zero_iff_of_nonneg
      (fun r (_ : r ∈ (Finset.univ : Finset (Fin (2 ^ (ell - 1))))) ↦ Nat.zero_le (s r).val)).mp h
  exact hh r

private theorem parentChild1_profiled0_intact0_fullChild0_zero_profile {ell L : ℕ} (mu : CompleteWord ell → ℕ)
    (hmass : ∑ s, mu s = L)
    (hgrade : ∀ s, 0 < mu s → CWCells.grade s = 0) :
    mu = fun s ↦ if s = (fun _ ↦ 0) then L else 0 := by
  classical
  have hs (s : CompleteWord ell) (h : s ≠ fun _ ↦ 0) : mu s = 0 := by
    by_contra hn
    exact h (parentChild1_profiled0_intact0_fullChild0_word_grade_zero s (hgrade s (Nat.pos_of_ne_zero hn)))
  have hz : mu (fun _ ↦ 0) = L := by
    calc
      mu (fun _ ↦ 0) = ∑ s, mu s := (Finset.sum_eq_single (fun _ ↦ 0)
        (fun s _ h ↦ hs s h) (by simp)).symm
      _ = L := hmass
  funext s
  by_cases h : s = fun _ ↦ 0
  · simp [h, hz]
  · simp [h, hs s h]

private theorem parentChild1_profiled0_intact0_fullChild0_flipLabel_eq_rev {ell : ℕ} (s : CompleteWord ell) :
    flipLabel s = fun r ↦ Fin.rev (s r) := by
  funext r
  apply Fin.ext
  simp [flipLabel, Fin.rev]

/-- Exact boundary profiles follow from mass, grade support, and the
boundary reversal identities, without requiring a hash stage. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_cell_boundary_profile_of_mass_support
    {half R ell L : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (c : Cell half R parent) (hhalf : half = 2 * 2 ^ (ell - 1))
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (hmass : ∀ i, ∑ s, mu i c s = L) (hboundary : BoundaryProfiles mu)
    (z : Fin 3) (hz : (c.2.val z).val = 0)
    (hg : ∀ i s, 0 < mu i c s → CWCells.grade s = (c.2.val i).val) :
    ∃ B : Boundary.Profile ell L,
      (∀ i, (c.2.val i).val = B.shape z i) ∧
      (∀ i, mu i c = B.mu z i) := by
  classical
  let cell := c
  have hm (i : Fin 3) : ∑ s, mu i cell s = L := hmass i
  have ht := cell.2.property.1.trans hhalf
  have hb (i : Fin 3) : (cell.2.val i).val ≤ 2 * 2 ^ (ell - 1) := by
    have h := (cell.2.val i).isLt
    rw [← hhalf]
    omega
  have hzero : mu z cell = fun s ↦ if s = (fun _ ↦ 0) then L else 0 :=
    parentChild1_profiled0_intact0_fullChild0_zero_profile _ (hm z) (fun s hs ↦ (hg z s hs).trans hz)
  have hrevs (s : CompleteWord ell) :
      flipLabel (flipLabel s) = s := by
    funext r
    apply Fin.ext
    simp only [flipLabel]
    have := (s r).isLt
    omega
  fin_cases z
  · let B : Boundary.Profile ell (L) :=
      ⟨(cell.2.val 1).val, hb 1, mu 1 cell, hm 1,
        fun s hs ↦ hg 1 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hz
      · rfl
      · change (cell.2.val 2).val = 2 * 2 ^ (ell - 1) - (cell.2.val 1).val
        change (cell.2.val 0).val = 0 at hz
        omega
    · intro i
      fin_cases i
      · exact hzero
      · rfl
      · funext s
        change mu 2 cell s = mu 1 cell (flipLabel s)
        rw [parentChild1_profiled0_intact0_fullChild0_flipLabel_eq_rev]
        exact hboundary.2.1 cell hz s
  · let B : Boundary.Profile ell (L) :=
      ⟨(cell.2.val 2).val, hb 2, mu 2 cell, hm 2,
        fun s hs ↦ hg 2 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · change (cell.2.val 0).val = 2 * 2 ^ (ell - 1) - (cell.2.val 2).val
        change (cell.2.val 1).val = 0 at hz
        omega
      · exact hz
      · rfl
    · intro i
      fin_cases i
      · funext s
        change mu 0 cell s = mu 2 cell (flipLabel s)
        rw [hboundary.2.2 cell hz, ← parentChild1_profiled0_intact0_fullChild0_flipLabel_eq_rev, hrevs]
      · exact hzero
      · rfl
  · let B : Boundary.Profile ell (L) :=
      ⟨(cell.2.val 0).val, hb 0, mu 0 cell, hm 0,
        fun s hs ↦ hg 0 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · rfl
      · change (cell.2.val 1).val = 2 * 2 ^ (ell - 1) - (cell.2.val 0).val
        change (cell.2.val 2).val = 0 at hz
        omega
      · exact hz
    · intro i
      fin_cases i
      · rfl
      · funext s
        change mu 1 cell s = mu 0 cell (flipLabel s)
        rw [parentChild1_profiled0_intact0_fullChild0_flipLabel_eq_rev]
        exact hboundary.1 cell hz s
      · exact hzero



open MME.Released116 MME.MoreAsymmetryExactSeed

/-- The child profile has exactly one count for each physical occurrence of
its split or its complementary split. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_released_116_integer_profile_mass :
    ∀ (i : Fin 3) (c : Cell 4 6 parent),
      ∑ w, integerProfile i c w =
        splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2) := by
  decide +kernel

/-- Positive child counts have the grade required by the integer-step interface. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_released_116_integer_profile_support :
    ∀ (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteWord 2),
      0 < integerProfile i c w → ∑ h, (w h).val = (c.2.val i).val := by
  decide +kernel


private theorem parentChild1_profiled0_intact0_fullChild0_scaled_boundary_profiles (k : ℕ) :
    BoundaryProfiles (fun i c w => k * integerProfile i c w) := by
  obtain ⟨h2, h0, h1⟩ := mme_released_116_integer_profile_boundary
  exact ⟨fun c hc w => congrArg (k * ·) (h2 c hc w),
    fun c hc w => congrArg (k * ·) (h0 c hc w),
    fun c hc w => congrArg (k * ·) (h1 c hc w)⟩

private theorem parentChild1_profiled0_intact0_fullChild0_boundary_dim_pos {ell L : ℕ} (B : Boundary.Profile ell L) :
    0 < B.dim := by
  have hm : 0 < L.factorial / ∏ w, (B.count w).factorial := by
    simpa only [Nat.multinomial, B.total] using Nat.multinomial_pos Finset.univ B.count
  exact Nat.mul_pos hm (by positivity)

private theorem parentChild1_profiled0_intact0_fullChild0_boundary_volume {ell L : ℕ} (B : Boundary.Profile ell L) (z : Fin 3) :
    B.a z * B.b z * B.c z = B.dim := by
  fin_cases z <;> simp [Boundary.Profile.a, Boundary.Profile.b, Boundary.Profile.c]

/-- Every physical boundary cell has an exact matrix extraction at every
integer replication. Shape and histogram equalities are retained so the
result can be assembled with the interior cells. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_released_116_physical_boundary_matrix_extraction
    (k : ℕ) (c : Cell 4 6 parent) (z : Fin 3)
    (hz : (c.2.val z).val = 0) :
    ∃ B : Boundary.Profile 2
        (k * (splitCount c.1 c.2 +
          splitCount c.1 (complement (parent_total c.1) c.2))),
      0 < B.dim ∧ B.a z * B.b z * B.c z = B.dim ∧
      (∀ i, (c.2.val i).val = B.shape z i) ∧
      (∀ i w, k * integerProfile i c w = B.mu z i w) ∧
      ∀ (K : Type u) [Field K],
        TensorObj.Restrict (MMObj K (B.a z) (B.b z) (B.c z))
          (CWCells.unbroken K 5 2
            (k * (splitCount c.1 c.2 +
              splitCount c.1 (complement (parent_total c.1) c.2)))
            (Equiv.refl _) (fun _ => Unit.unit)
            (fun _ i => (c.2.val i).val)
            (fun i _ w => k * integerProfile i c w)) := by
  have hmass (i : Fin 3) : ∑ w, k * integerProfile i c w =
      k * (splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)) := by
    rw [← Finset.mul_sum, parentChild1_profiled0_intact0_fullChild0_mme_released_116_integer_profile_mass]
  have hg (i : Fin 3) (w : CompleteWord 2) (hw : 0 < k * integerProfile i c w) :
      CWCells.grade w = (c.2.val i).val := by
    exact parentChild1_profiled0_intact0_fullChild0_mme_released_116_integer_profile_support i c w (Nat.pos_of_mul_pos_left hw)
  obtain ⟨B, hshape, hmu⟩ := parentChild1_profiled0_intact0_fullChild0_mme_cell_boundary_profile_of_mass_support c rfl
    (fun i c w => k * integerProfile i c w) hmass (parentChild1_profiled0_intact0_fullChild0_scaled_boundary_profiles k) z hz hg
  refine ⟨B, parentChild1_profiled0_intact0_fullChild0_boundary_dim_pos B, parentChild1_profiled0_intact0_fullChild0_boundary_volume B z, hshape,
    fun i w => congrFun (hmu i) w, ?_⟩
  intro K _
  have h := mme_recursive_yz_boundary_actual_matrix_extraction (K := K) B z
  have hmu_point (i : Fin 3) (w : CompleteWord 2) :
      k * integerProfile i c w = B.mu z i w := congrFun (hmu i) w
  simpa only [Boundary.Profile.tensor, hshape, hmu_point] using h



open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false

private theorem parentChild1_profiled0_intact0_fullChild0_scaled_boundary_log_lower {ell L : ℕ}
    (B : Profile ell L) (hL : 0 < L) (k : ℕ) (hk : 0 < k)
    (C : Profile ell (L * k)) (hcount : ∀ s, C.count s = B.count s * k) :
    (k : ℝ) * ((L : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) +
      ((∑ s, B.count s * ones s : ℕ) : ℝ) * Real.log 5) -
      (Fintype.card (CompleteWord ell) : ℝ) *
        Real.log (6 * ((L * k + 1 : ℕ) : ℝ)) ≤ Real.log (C.dim : ℝ) := by
  classical
  have hm : 0 < ∑ s, B.count s := by rw [B.total]; exact hL
  have h := mme_dwz_multinomial_entropy_polynomial_lower B.count k hk hm
  have hc : (fun s ↦ B.count s * k) = C.count := by funext s; exact (hcount s).symm
  rw [B.total, hc] at h
  have hmulti : (0 : ℝ) < Nat.multinomial Finset.univ C.count := by
    exact_mod_cast Nat.multinomial_pos Finset.univ C.count
  have hp : (0 : ℝ) < 6 * ((L * k + 1 : ℕ) : ℝ) := by positivity
  have hl := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp, Real.log_mul (ne_of_gt (pow_pos hp _)) (ne_of_gt hmulti),
    Real.log_pow] at hl
  have hone : ∑ s, C.count s * ones s = (∑ s, B.count s * ones s) * k := by
    simp only [hcount, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hd : (C.dim : ℝ) =
      (Nat.multinomial Finset.univ C.count : ℝ) *
        (5 : ℝ) ^ (∑ s, C.count s * ones s) := by
    simp only [Profile.dim, Nat.multinomial, C.total, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [hd, Real.log_mul (ne_of_gt hmulti) (by positivity), Real.log_pow, hone]
  push_cast at hl ⊢
  nlinarith only [hl]

/-- Replication of a boundary histogram attains its entropy and CW-letter rate;
the threshold is uniform over all boundary profiles with that histogram. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_boundary_scaled_volume_rate {ell L : ℕ}
    (B : Profile ell L) (hL : 0 < L) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ C : Profile ell (L * k),
      (∀ s, C.count s = B.count s * k) →
      (k : ℝ) * ((L : ℝ) * Real.log 2 *
          mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) +
        ((∑ s, B.count s * ones s : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.dim : ℝ) := by
  classical
  let a : ℝ := Fintype.card (CompleteWord ell)
  have ha : 0 ≤ a := by positivity
  have habs := mme_log_sqrt_loss_eventually_le_linear a 0
    (a * Real.log (6 * ((L : ℝ) + 1))) delta hdelta
  filter_upwards [habs, eventually_gt_atTop 0] with k hk hkpos
  intro C hcount
  have hlog := parentChild1_profiled0_intact0_fullChild0_scaled_boundary_log_lower B hL k hkpos C hcount
  have hpoly : (6 : ℝ) * ((L * k + 1 : ℕ) : ℝ) ≤
      (6 * ((L : ℝ) + 1)) * ((k : ℝ) + 1) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L,
      show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hlogs := Real.log_le_log (by positivity : (0 : ℝ) <
    6 * ((L * k + 1 : ℕ) : ℝ)) hpoly
  rw [Real.log_mul (show (6 * ((L : ℝ) + 1)) ≠ 0 by positivity)
    (show ((k : ℝ) + 1) ≠ 0 by positivity)] at hlogs
  have hscaled := mul_le_mul_of_nonneg_left hlogs ha
  change a * Real.log ((k : ℝ) + 1) + 0 * Real.sqrt ((k : ℝ) + 1) +
    a * Real.log (6 * ((L : ℝ) + 1)) ≤ (k : ℝ) * delta at hk
  change (k : ℝ) * _ - a * _ ≤ _ at hlog
  nlinarith only [hlog, hscaled, hk]


private theorem parentChild1_profiled0_intact0_fullChild0_released_boundary_mass_pos (c : Cell 4 6 parent) :
    0 < splitCount c.1 c.2 +
      splitCount c.1 (complement (parent_total c.1) c.2) := by
  revert c
  decide +kernel

private theorem parentChild1_profiled0_intact0_fullChild0_boundary_count_from_mu {ell L M : ℕ}
    (B : Boundary.Profile ell L) (C : Boundary.Profile ell M)
    (z : Fin 3) (k : ℕ) (h : ∀ i w, C.mu z i w = B.mu z i w * k) :
    ∀ w, C.count w = B.count w * k := by
  intro w
  fin_cases z
  · simpa [Boundary.Profile.mu] using h 1 w
  · simpa [Boundary.Profile.mu] using h 2 w
  · simpa [Boundary.Profile.mu] using h 0 w

/-- Each released boundary cell has physical matrix extractions attaining the
entropy and CW-letter rate of its exact integer histogram. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_released_116_boundary_physical_volume_rate
    (c : Cell 4 6 parent) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 2
        (splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)),
      (∀ i w, integerProfile i c w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ C : Boundary.Profile 2
          (k * (splitCount c.1 c.2 +
            splitCount c.1 (complement (parent_total c.1) c.2))),
        0 < C.dim ∧ C.a z * C.b z * C.c z = C.dim ∧
        (∀ i, (c.2.val i).val = C.shape z i) ∧
        (∀ i w, k * integerProfile i c w = C.mu z i w) ∧
        (k : ℝ) *
          (((splitCount c.1 c.2 +
              splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits
              (fun w ↦ (B.count w : ℝ) /
                ((splitCount c.1 c.2 +
                  splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.a z * C.b z * C.c z : ℕ) ∧
        ∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K (C.a z) (C.b z) (C.c z))
            (CWCells.unbroken K 5 2
              (k * (splitCount c.1 c.2 +
                splitCount c.1 (complement (parent_total c.1) c.2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => (c.2.val i).val)
              (fun i _ w => k * integerProfile i c w)) := by
  have hbase := parentChild1_profiled0_intact0_fullChild0_mme_released_116_physical_boundary_matrix_extraction.{u} 1 c z hz
  rw [Nat.one_mul] at hbase
  simp only [Nat.one_mul] at hbase
  obtain ⟨B, _, _, _, hBmu, _⟩ := hbase
  refine ⟨B, hBmu, ?_⟩
  have hrate := parentChild1_profiled0_intact0_fullChild0_mme_boundary_scaled_volume_rate B (parentChild1_profiled0_intact0_fullChild0_released_boundary_mass_pos c)
    delta hdelta
  have hrate' : ∀ᶠ k : ℕ in atTop,
      ∀ C : Boundary.Profile 2 (k * (splitCount c.1 c.2 +
          splitCount c.1 (complement (parent_total c.1) c.2))),
        (∀ w, C.count w = B.count w * k) →
        (k : ℝ) *
          (((splitCount c.1 c.2 +
              splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits
              (fun w ↦ (B.count w : ℝ) /
                ((splitCount c.1 c.2 +
                  splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.dim : ℝ) := by
    filter_upwards [hrate] with k hk
    rw [Nat.mul_comm (splitCount c.1 c.2 +
      splitCount c.1 (complement (parent_total c.1) c.2)) k] at hk
    exact hk
  filter_upwards [hrate'] with k hk
  obtain ⟨C, hpos, hvol, hshape, hmu, hextract⟩ :=
    parentChild1_profiled0_intact0_fullChild0_mme_released_116_physical_boundary_matrix_extraction k c z hz
  have hcount := parentChild1_profiled0_intact0_fullChild0_boundary_count_from_mu B C z k (by
    intro i w
    rw [← hmu i w, ← hBmu i w, Nat.mul_comm])
  refine ⟨C, hpos, hvol, hshape, hmu, ?_, hextract⟩
  rw [hvol]
  exact hk C hcount



open MME
set_option autoImplicit false

/-- Full symmetrization turns a matrix tensor of volume V into a square
matrix tensor with each dimension V squared. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_MMObj_sixSymmetrization_iso {K : Type u} [Field K] (a b c : ℕ) :
    TensorObj.Isomorphic (sixSymmetrization (MMObj K a b c))
      (MMObj K ((a * b * c) ^ 2) ((a * b * c) ^ 2) ((a * b * c) ^ 2)) := by
  let V := a * b * c
  have hcyc := TensorQ.toQ_eq_iff.mpr
    (mme_MMObj_cyclicSymmetrization_iso (K := K) a b c)
  have hswap := TensorQ.toQ_eq_iff.mpr
    (mme_MMObj_permObj_swapFirstTwo (K := K) V V V)
  apply TensorQ.toQ_eq_iff.mp
  rw [sixSymmetrization, TensorQ.toQ_kron, ← TensorQ.permAut_toQ,
    hcyc, TensorQ.permAut_toQ, hswap]
  have hmul := TensorQ.toQ_eq_iff.mpr (MMObj_kron_iso (K := K) V V V V V V)
  simpa only [TensorQ.toQ_kron, pow_two] using hmul

/-- A positive matrix extraction yields a six-symmetric extraction whose tau
weight retains six times its log-volume bound, for nonnegative tau. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_matrix_extraction_six_volume_weight
    {K : Type u} [Field K] {T : TensorObj K 3} (a b c : ℕ)
    (hrestrict : TensorObj.Restrict (MMObj K a b c) T)
    (hpos : 0 < a * b * c) (rate tau : ℝ) (htau : 0 ≤ tau)
    (hrate : rate ≤ Real.log (a * b * c : ℕ)) :
    TensorObj.Restrict
      (MMObj K ((a * b * c) ^ 2) ((a * b * c) ^ 2) ((a * b * c) ^ 2))
      (sixSymmetrization T) ∧
    Real.exp (6 * tau * rate) ≤
      ((((a * b * c) ^ 2 * (a * b * c) ^ 2 * (a * b * c) ^ 2 : ℕ) : ℝ) ^ tau) := by
  constructor
  · exact (parentChild1_profiled0_intact0_fullChild0_mme_MMObj_sixSymmetrization_iso (K := K) a b c).2.trans
      (mme_sixSymmetrization_restrict hrestrict)
  · have hv : (0 : ℝ) < (a * b * c : ℕ) := by exact_mod_cast hpos
    have hpow : (a * b * c) ^ 2 * (a * b * c) ^ 2 * (a * b * c) ^ 2 =
        (a * b * c) ^ 6 := by ring
    rw [hpow, Nat.cast_pow, Real.rpow_def_of_pos (pow_pos hv _), Real.log_pow]
    apply Real.exp_le_exp.mpr
    norm_num only [Nat.cast_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hrate (show 0 ≤ 6 * tau by positivity)]


/-- The released boundary cells supply square matrices in the full
six-symmetric physical tensor, with their entropy and letter weight. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_released_116_boundary_six_weight_rate
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
            ((M * M * M : ℕ) : ℝ) ^ tau := by
  obtain ⟨B, hmu, hrate⟩ :=
    parentChild1_profiled0_intact0_fullChild0_mme_released_116_boundary_physical_volume_rate.{u} c z hz delta hdelta
  refine ⟨B, hmu, ?_⟩
  filter_upwards [hrate] with k hk
  obtain ⟨C, hpos, hvol, _, _, hlog, hextract⟩ := hk
  have hv : 0 < C.a z * C.b z * C.c z := by rw [hvol]; exact hpos
  refine ⟨(C.a z * C.b z * C.c z) ^ 2, pow_pos hv _, ?_, ?_⟩
  · intro K _
    exact (parentChild1_profiled0_intact0_fullChild0_mme_MMObj_sixSymmetrization_iso (K := K) (C.a z) (C.b z) (C.c z)).2.trans
      (mme_sixSymmetrization_restrict (hextract K))
  · intro tau htau
    exact (parentChild1_profiled0_intact0_fullChild0_mme_matrix_extraction_six_volume_weight (K := ULift.{u} ℚ)
      (C.a z) (C.b z) (C.c z) (hextract (ULift.{u} ℚ)) hv _ tau htau hlog).2



open MME BigOperators
set_option autoImplicit false

private theorem parentChild1_profiled0_intact0_fullChild0_kron_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft :
      P.le (TensorQ.toQ X * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright :
      P.le (TensorQ.toQ X' * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright

private theorem parentChild1_profiled0_intact0_fullChild0_kronFin_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d) :
    ∀ (n : ℕ) (X Y : Fin n → TensorObj K d),
      (∀ i, TensorObj.Restrict (X i) (Y i)) →
      TensorObj.Restrict (TensorObj.kronFin n X) (TensorObj.kronFin n Y) := by
  intro n
  induction n with
  | zero =>
      intro X Y h
      exact TensorObj.Restrict.refl _
  | succ n ih =>
      intro X Y h
      change TensorObj.Restrict
        (TensorObj.kron (X 0)
          (TensorObj.kronFin n (fun i ↦ X i.succ)))
        (TensorObj.kron (Y 0)
          (TensorObj.kronFin n (fun i ↦ Y i.succ)))
      exact parentChild1_profiled0_intact0_fullChild0_kron_restrict_for_tau_product hd (h 0)
        (ih (fun i ↦ X i.succ) (fun i ↦ Y i.succ) (fun i ↦ h i.succ))

/-- Six-symmetrization commutes with finite tensor products, up to actual
mutual restrictions. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_sixSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i => sixSymmetrization (T i)))
      (sixSymmetrization (TensorObj.kronFin n T)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [mme_toQ_kronFin, sixSymmetrization,
    cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    ← TensorQ.permAut_toQ, map_prod, map_mul, Finset.prod_mul_distrib]


/-- Finite six-symmetric square-matrix extractions combine without a loss in
exponential weight. -/
private theorem parentChild1_profiled0_intact0_fullChild0_mme_six_square_product_weight {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (M : Fin n → ℕ) (rate : Fin n → ℝ) (tau : ℝ)
    (hextract : ∀ i, TensorObj.Restrict (MMObj K (M i) (M i) (M i))
      (sixSymmetrization (T i)))
    (hweight : ∀ i, Real.exp (rate i) ≤ ((M i * M i * M i : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict (MMObj K (∏ i, M i) (∏ i, M i) (∏ i, M i))
      (sixSymmetrization (TensorObj.kronFin n T)) ∧
    Real.exp (∑ i, rate i) ≤
      ((((∏ i, M i) * (∏ i, M i) * (∏ i, M i) : ℕ) : ℝ) ^ tau) := by
  constructor
  · exact (mme_kronFin_MMObj_iso (K := K) n M M M).2.trans
      ((parentChild1_profiled0_intact0_fullChild0_kronFin_restrict_for_tau_product (by decide) n _ _ hextract).trans
        (parentChild1_profiled0_intact0_fullChild0_mme_sixSymmetrization_kronFin_isomorphic T).1)
  · rw [Real.exp_sum]
    have hprod := Finset.prod_le_prod
      (fun i (_ : i ∈ Finset.univ) ↦ (Real.exp_pos (rate i)).le)
      (fun i (_ : i ∈ Finset.univ) ↦ hweight i)
    calc
      ∏ i, Real.exp (rate i) ≤ ∏ i, ((M i * M i * M i : ℕ) : ℝ) ^ tau := hprod
      _ = (∏ i, ((M i * M i * M i : ℕ) : ℝ)) ^ tau := by
        rw [Real.finset_prod_rpow]
        intro i _
        positivity
      _ = _ := by
        simp only [Nat.cast_mul, Nat.cast_prod, Finset.prod_mul_distrib]


/-- Any finite family of released boundary cells has a common replication
threshold and a single square-matrix extraction with the summed weight rate. -/
private theorem parentChild1_profiled0_intact0_mme_released_116_boundary_product_weight_rate
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
            ((M * M * M : ℕ) : ℝ) ^ tau := by
  classical
  have h := fun r ↦ parentChild1_profiled0_intact0_fullChild0_mme_released_116_boundary_six_weight_rate.{u}
    (c r) (z r) (hz r) delta hdelta
  choose B hmu hrate using h
  refine ⟨B, hmu, ?_⟩
  filter_upwards [Filter.eventually_all.2 hrate] with k hk
  choose M hpos hextract hweight using hk
  refine ⟨∏ r, M r, Finset.prod_pos (fun r _ ↦ hpos r), ?_, ?_⟩
  · intro K _
    exact (parentChild1_profiled0_intact0_fullChild0_mme_six_square_product_weight (K := K) _ M _ 0
      (fun r ↦ hextract r K) (fun r ↦ hweight r 0 le_rfl)).1
  · intro tau htau
    exact (parentChild1_profiled0_intact0_fullChild0_mme_six_square_product_weight (K := ULift.{u} ℚ) _ M _ tau
      (fun r ↦ hextract r (ULift.{u} ℚ)) (fun r ↦ hweight r tau htau)).2



open MME MME.CompleteSplit MME.RecursiveYZ MME.Released116
open MME.MoreAsymmetryExactSeed

set_option autoImplicit false

namespace MME.Released116

/-- The released mass of either outer atom in a 112 child. -/
def child112OuterCount (r : Fin 6) : ℕ :=
  ((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
    (0, [], 0)).2.2

/-- Exact marginal counts of the released 112 child, before cell scaling. -/
def child112Marginal (r : Fin 6) (i : Fin 3) (w : CompleteWord 2) : ℕ :=
  if i = 2 then
    if w = ![0, 2] ∨ w = ![2, 0] then child112OuterCount r
    else if w = ![1, 1] then denominator - 2 * child112OuterCount r else 0
  else
    if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0

/-- All six released parameters lie strictly inside the four-atom family. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_parameter_bounds :
    ∀ r : Fin 6, 0 < child112OuterCount r ∧
      2 * child112OuterCount r < denominator := by
  decide +kernel

/-- The integer reconstruction has uniform X and Y marginals and the exact
three-word Z marginal determined by the released outer-atom count. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_marginal_formula :
    ∀ (r : Fin 6) (c : Split),
      (c.val 0).val = 1 → (c.val 1).val = 1 → (c.val 2).val = 2 →
      ∀ (i : Fin 3) (w : CompleteWord 2),
        childMarginal r c i w = child112Marginal r i w := by
  have h :
      ∀ (r : Fin 6) (i : Fin 3) (w : CompleteWord 2),
        childMarginal r ⟨![1, 1, 2], by decide⟩ i w =
          child112Marginal r i w := by
    decide +kernel
  intro r c h0 h1 h2 i w
  have hc : c = ⟨![1, 1, 2], by decide⟩ := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  subst c
  exact h r i w

/-- Cell multiplicity scales the same exact 112 marginal in every mode. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_integer_profile
    (c : Cell 4 6 parent)
    (h0 : (c.2.val 0).val = 1) (h1 : (c.2.val 1).val = 1)
    (h2 : (c.2.val 2).val = 2) (i : Fin 3) (w : CompleteWord 2) :
    integerProfile i c w =
      seed.region.getD c.1.val 0 *
        (splitWeight c.1 c.2 +
          splitWeight c.1 (complement (parent_total c.1) c.2)) *
        denominator * child112Marginal c.1 i w := by
  unfold integerProfile
  rw [parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_marginal_formula c.1 c.2 h0 h1 h2]

/-- Reversing the two elementary factors preserves every released 112 marginal. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_marginal_reverse :
    ∀ (r : Fin 6) (i : Fin 3) (w : CompleteWord 2),
      child112Marginal r i (fun j => w (Fin.rev j)) = child112Marginal r i w := by
  decide +kernel

/-- The reconstruction is normalized before the physical cell multiplier. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_marginal_mass :
    ∀ (r : Fin 6) (i : Fin 3),
      ∑ w : CompleteWord 2, child112Marginal r i w = denominator := by
  decide +kernel

end MME.Released116


open MME.Released116 MME.CompleteSplit112 Filter

/-- The actual six parameters satisfy the balance condition required by the
uniform induced-family construction. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_hash_balance :
    ∀ r : Fin 6, 341 * (2 * child112OuterCount r) <
      100 * (denominator - 2 * child112OuterCount r) := by
  decide +kernel

/-- The released marginal agrees with the parametric coupled-family profile
at its own exact rational parameter. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_parametric_probability :
    ∀ (r : Fin 6) (i : Fin 3) (w : CompleteWord 2),
      (child112Marginal r i w : ℚ) / denominator =
        profileProbability ((child112OuterCount r : ℚ) / denominator) i w := by
  decide +kernel


/-- Each released region has actual induced families on its exact integer
subsequence, retaining the separate and joint directional capacities. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_cofinal_induced_families (r : Fin 6) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N := denominator * m
        let L := (2 * child112OuterCount r) * m
        let G := (denominator - 2 * child112OuterCount r) * m
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
          0 < A ∧ H ≤ 4 ^ N ∧
          ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
          (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) := by
  let D := denominator
  let l := 2 * child112OuterCount r
  let g := D - l
  have hl : 0 < l := by
    dsimp [l]
    exact Nat.mul_pos (by decide) (parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_parameter_bounds r).1
  have hsum : l + g = D := by
    have hlt := (parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_parameter_bounds r).2
    dsimp [l, g, D]
    omega
  have hbalance : 341 * l < 100 * g := parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_hash_balance r
  obtain ⟨C, hC, hlarge⟩ := mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
    (fun n => l * (n / D)) (fun n => g * (n / D))
  refine ⟨C, hC, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hlarge
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with m hm
  have hmpos : 0 < m := by omega
  have hNm : N₀ ≤ D * m := by dsimp [D, denominator]; omega
  have hdiv : D * m / D = m := by dsimp [D, denominator]; omega
  have hLpos : 0 < l * m := Nat.mul_pos hl hmpos
  have hLG : l * m + g * m = D * m := by rw [← Nat.add_mul, hsum]
  have hbal : 341 * (l * m) < 100 * (g * m) := by
    simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_right hbalance hmpos
  have hextract := hN₀ (D * m) hNm
  dsimp only at hextract
  simp only [hdiv] at hextract
  obtain ⟨A, H, family, hH, hA, hmiddle⟩ := hextract ⟨hLpos, hLG, hbal⟩
  rw [hdiv] at family
  have hcapacity := mme_primary_hash_uniform_stars_joint_directional_capacity
    (D * m) (l * m) (g * m) A H hLG C hA hmiddle
  have hZpos :
      (0 : ℝ) < (Nat.choose (2 * (D * m)) (l * m) *
        Nat.choose (2 * (D * m) - l * m) (l * m) : ℕ) := by
    exact_mod_cast Nat.mul_pos
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m)))
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m) - l * m))
  have hApos : (0 : ℝ) < A :=
    lt_of_lt_of_le (mul_pos hZpos (Real.exp_pos _)) hA
  exact ⟨A, H, family, by exact_mod_cast hApos, hH, hA, hcapacity.2.2⟩



/-- A family with the released counts lies in the actual exact-profile
intact 112 tensor, with its full common matrix volume. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_intact_family_certificate
    (r : Fin 6) (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily (denominator * m)
      ((2 * child112OuterCount r) * m)
      ((denominator - 2 * child112OuterCount r) * m) A H)
    (K : Type u) [Field K] :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (CWCells.unbroken K 5 2 (2 * (denominator * m)) (Equiv.refl _)
          (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
          (fun i _ w => 2 * m * child112Marginal r i w))
        A H (5 ^ (4 * ((denominator - 2 * child112OuterCount r) * m) +
          2 * ((2 * child112OuterCount r) * m)))) := by
  let beta (i : Fin 3) : Profile 2 := {
    level_pos := by decide
    probability w := (child112Marginal r i w : ℝ) / denominator
    nonnegative w := by positivity
    sum_eq_one := by
      rw [← Finset.sum_div, ← Nat.cast_sum, parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_marginal_mass]
      norm_num [denominator] }
  have hbeta (i : Fin 3) (w : CompleteWord 2) :
      (beta i).probability w =
        (profileProbability ((child112OuterCount r : ℚ) / denominator) i w : ℝ) := by
    dsimp [beta]
    have h := congrArg (fun x : ℚ => (x : ℝ))
      (parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_parametric_probability r i w)
    simpa only [Rat.cast_div, Rat.cast_natCast] using h
  have hLG :
      (2 * child112OuterCount r) * m +
        (denominator - 2 * child112OuterCount r) * m = denominator * m := by
    rw [← Nat.add_mul, Nat.add_sub_of_le
      (parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_parameter_bounds r).2.le]
  have hLp :
      (((2 * child112OuterCount r) * m : ℕ) : ℚ) =
        ((2 * (denominator * m) : ℕ) : ℚ) *
          ((child112OuterCount r : ℚ) / denominator) := by
    push_cast
    norm_num [denominator]
    ring
  obtain ⟨certificate⟩ :=
    mme_complete_split_112_coupled_restricted_family_certificate
      (K := K) 5 ((child112OuterCount r : ℚ) / denominator)
      hLG hLp family beta hbeta 0
  have hmu (i : Fin 3) (w : CompleteWord 2) :
      ((2 * m * child112Marginal r i w : ℕ) : ℝ) =
        ((2 * (denominator * m) : ℕ) : ℝ) * (beta i).probability w := by
    dsimp [beta]
    push_cast
    norm_num [denominator]
    ring
  exact ⟨{
    star := certificate.star
    restrict := certificate.restrict.trans
      ((mme_complete_split_112_canonical_profile_router K 5 beta 0
        (2 * (denominator * m))).trans
        (mme_complete_split_112_canonical_power_restricts_from_intact K 5
          (2 * (denominator * m)) beta
          (fun i w => 2 * m * child112Marginal r i w) hmu))
    certificate := certificate.certificate
  }⟩


/-- Cofinal matrix extractions from the actual released exact 112 profiles.
The induced family supplies both directional capacities and the explicit
copy bound after cyclic symmetrization. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_cofinal_matrix_extraction (r : Fin 6) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N := denominator * m
        let L := (2 * (((seed.children.find?
          (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
        let G := (denominator - 2 * (((seed.children.find?
          (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
          0 < A ∧ H ≤ 4 ^ N ∧
          ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
          (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) ∧
          ∀ (K : Type u) [Field K], ∃ (k : ℕ) (a b c : Fin k → ℕ),
            0 < k ∧
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
              (cyclicSymmetrization
                (CWCells.unbroken K 5 2 (2 * N) (Equiv.refl _)
                  (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                  (fun i _ w => 2 * m * childMarginal r ⟨![1, 1, 2], by decide⟩ i w))) ∧
            (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
                Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) ≤
              (k : ℝ) ∧
            ∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3 := by
  obtain ⟨C, hC, hfamilies⟩ := parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_cofinal_induced_families r
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfamilies] with m hm
  obtain ⟨A, H, family, hApos, hH, hA, hAH⟩ := hm
  refine ⟨A, H, family, hApos, hH, hA, hAH, ?_⟩
  intro K _
  obtain ⟨certificate⟩ := parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_intact_family_certificate
    r m A H family K
  obtain ⟨k, a, b, c, hrestrict, hcount, hvolume⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction certificate family.hHpos
  have hAr : (0 : ℝ) < A := by exact_mod_cast hApos
  have hHr : (0 : ℝ) < H := by exact_mod_cast family.hHpos
  have hpositive : 0 < (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) := by positivity
  have hk : 0 < k := by exact_mod_cast hpositive.trans_le hcount
  refine ⟨k, a, b, c, hk, ?_, hcount, hvolume⟩
  simpa only [parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_marginal_formula r
    ⟨![1, 1, 2], by decide⟩ rfl rfl rfl] using hrestrict

/-- The released 112 extraction retains the entropy rate of the Z marginal
and both unshared directions, with the explicit final sublinear loss. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_cofinal_matrix_log_rate
    (r : Fin 6) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      let N := denominator * m
      let L := (2 * (((seed.children.find?
        (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * (((seed.children.find?
        (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
      let p : ℝ := ((((seed.children.find?
        (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2) : ℝ) / denominator
      ∃ A H : ℕ, 0 < A ∧ 0 < H ∧ H ≤ 4 ^ N ∧
        ((2 * N : ℕ) : ℝ) *
            (Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] - delta) ≤
          Real.log (A : ℝ) ∧
        ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
          Real.log ((A : ℝ) * (H : ℝ)) ∧
        ∀ (K : Type u) [Field K], ∃ (k : ℕ) (a b c : Fin k → ℕ),
          0 < k ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (cyclicSymmetrization
              (CWCells.unbroken K 5 2 (2 * N) (Equiv.refl _)
                (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => 2 * m * childMarginal r ⟨![1, 1, 2], by decide⟩ i w))) ∧
          (∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3) ∧
          ((2 * N : ℕ) : ℝ) *
              (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) -
                3 * delta) -
              100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤ Real.log (k : ℝ) := by
  obtain ⟨C, _hC, hfamilies⟩ := parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_cofinal_matrix_extraction r
  let l := 2 * child112OuterCount r
  let g := denominator - l
  have hsum : l + g = denominator := by
    exact Nat.add_sub_of_le (parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_parameter_bounds r).2.le
  have hD : 0 < l + g := by rw [hsum]; decide
  have hp : (l : ℝ) / (2 * (denominator : ℝ)) =
      (child112OuterCount r : ℝ) / denominator := by
    dsimp [l]
    push_cast
    norm_num [denominator]
    ring
  have he := mme_complete_split_112_outer_star_entropy_rate l g hD C delta hdelta
  simp only [hsum, hp] at he
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_central_binomial_sqrt_loss_log_rate C delta hdelta)
  filter_upwards [hfamilies, he, eventually_ge_atTop n₀]
    with m hm hme hmn
  dsimp only at hm hme ⊢
  obtain ⟨A, H, family, hApos, hH, hA, hAH, hextract⟩ := hm
  have hAr : (0 : ℝ) < A := by exact_mod_cast hApos
  have hHr : (0 : ℝ) < H := by exact_mod_cast family.hHpos
  have hNm : n₀ ≤ denominator * m := by dsimp [denominator]; omega
  have hlogAH := hn₀ (denominator * m) hNm
    ((A : ℝ) * (H : ℝ)) (mul_pos hAr hHr)
    (by simpa only [mul_assoc] using hAH)
  have hlogAH' : ((2 * (denominator * m) : ℕ) : ℝ) * (Real.log 2 - delta) ≤
      Real.log ((A : ℝ) * (H : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlogAH
  have hlogA := hme (A : ℝ) hAr hA
  refine ⟨A, H, hApos, family.hHpos, hH, hlogA, hlogAH', ?_⟩
  intro K _
  obtain ⟨k, a, b, c, hk, hrestrict, hcount, hvolume⟩ := hextract K
  refine ⟨k, a, b, c, hk, hrestrict, hvolume, ?_⟩
  have hpositive : 0 < (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) := by positivity
  have hlog := Real.log_le_log hpositive hcount
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_exp] at hlog
  rw [Real.log_mul hAr.ne' hHr.ne'] at hlogAH'
  norm_num only [Nat.cast_ofNat] at hlog
  dsimp only [child112OuterCount] at hlogA
  nlinarith only [hlog, hlogA, hlogAH']

namespace MME.Released116

private def parentChild1_profiled0_intact0_fullChild1_child112Split : Split := ⟨![1, 1, 2], by decide⟩

/-- The physical cell multiplier after separating one factor of the
released denominator. Even replication makes the family scale integral. -/
private def parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale (r : Fin 6) : ℕ :=
  seed.region.getD r.val 0 *
    (splitWeight r parentChild1_profiled0_intact0_fullChild1_child112Split +
      splitWeight r (complement (parent_total r) parentChild1_profiled0_intact0_fullChild1_child112Split)) * denominator

private theorem parentChild1_profiled0_intact0_fullChild1_child112_physical_scale_pos :
    ∀ r : Fin 6, 0 < parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r := by
  decide +kernel

private theorem parentChild1_profiled0_intact0_fullChild1_child112_physical_size (r : Fin 6) (k : ℕ) :
    2 * (denominator * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r)) =
      (2 * k) * (splitCount r parentChild1_profiled0_intact0_fullChild1_child112Split +
        splitCount r (complement (parent_total r) parentChild1_profiled0_intact0_fullChild1_child112Split)) := by
  unfold parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale splitCount
  ring

private theorem parentChild1_profiled0_intact0_fullChild1_child112_physical_histogram
    (r : Fin 6) (k : ℕ) (i : Fin 3) (w : CompleteWord 2) :
    2 * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r) * childMarginal r parentChild1_profiled0_intact0_fullChild1_child112Split i w =
      (2 * k) * integerProfile i ⟨r, parentChild1_profiled0_intact0_fullChild1_child112Split⟩ w := by
  unfold parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale integerProfile
  ring

end MME.Released116


/-- At every sufficiently large even replication, all six regions admit
the checked 112 extraction on their physical integer profiles. The source
length is the sum of the complementary split multiplicities. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_simultaneous_physical_extraction
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
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
      ∃ A H : ℕ, 0 < A ∧ 0 < H ∧ H ≤ 4 ^ N ∧
        ((2 * N : ℕ) : ℝ) *
            (Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] - delta) ≤
          Real.log (A : ℝ) ∧
        ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
          Real.log ((A : ℝ) * (H : ℝ)) ∧
        ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
          0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (cyclicSymmetrization
              (CWCells.unbroken K 5 2
                ((2 * k) * (splitCount r (⟨![1, 1, 2], by decide⟩ : Split) +
                  splitCount r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))))
                (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => (2 * k) * integerProfile i ⟨r, (⟨![1, 1, 2], by decide⟩ : Split)⟩ w))) ∧
          (∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3) ∧
          ((2 * N : ℕ) : ℝ) *
              (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) -
                3 * delta) -
              100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
            Real.log (copies : ℝ) := by
  apply Filter.eventually_all.mpr
  intro r
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    (parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_cofinal_matrix_log_rate r delta hdelta)
  filter_upwards [eventually_ge_atTop m₀] with k hk
  have hscale := parentChild1_profiled0_intact0_fullChild1_child112_physical_scale_pos r
  have hlarge : m₀ ≤ k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r := by nlinarith
  have h := hm₀ (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r) hlarge
  dsimp only at h ⊢
  obtain ⟨A, H, hA, hH, hHbound, hlogA, hlogAH, hextract⟩ := h
  refine ⟨A, H, hA, hH, hHbound, hlogA, hlogAH, ?_⟩
  intro K _
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hrate⟩ := hextract K
  refine ⟨copies, a, b, c, hcopies, ?_, hvolume, hrate⟩
  have hsize := parentChild1_profiled0_intact0_fullChild1_child112_physical_size r k
  have hhist := parentChild1_profiled0_intact0_fullChild1_child112_physical_histogram r k
  dsimp only [parentChild1_profiled0_intact0_fullChild1_child112Split] at hsize hhist
  rw [← hsize]
  simp only [← hhist]
  exact hrestrict


open BigOperators

/-- Swapping and multiplying a cyclic extraction squares its copy count
and common volume. Its logarithmic copy bound gives a six-symmetric weight
bound without requiring the individual matrices to be square. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_cyclic_constant_volume_extraction_six_weight
    {K : Type u} [Field K] {T : TensorObj K 3} {k V : ℕ}
    (a b c : Fin k → ℕ) (hk : 0 < k)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (cyclicSymmetrization T))
    (hvolume : ∀ j, a j * b j * c j = V)
    (L tau : ℝ) (hlog : L ≤ Real.log (k : ℝ)) :
    ∃ (copies : ℕ) (a' b' c' : Fin copies → ℕ),
      0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization T) ∧
      (∀ j, a' j * b' j * c' j = V ^ 2) ∧
      Real.exp (2 * L) * (((V ^ 2 : ℕ) : ℝ) ^ tau) ≤
        ∑ j, (((a' j * b' j * c' j : ℕ) : ℝ) ^ tau) := by
  let a' := fun r : Fin (k * k) => a (finProdFinEquiv.symm r).1 * c (finProdFinEquiv.symm r).2
  let b' := fun r : Fin (k * k) => b (finProdFinEquiv.symm r).1 * b (finProdFinEquiv.symm r).2
  let c' := fun r : Fin (k * k) => c (finProdFinEquiv.symm r).1 * a (finProdFinEquiv.symm r).2
  have hvol (j : Fin (k * k)) : a' j * b' j * c' j = V ^ 2 := by
    dsimp only [a', b', c']
    calc
      _ = (a (finProdFinEquiv.symm j).1 * b (finProdFinEquiv.symm j).1 *
          c (finProdFinEquiv.symm j).1) *
        (a (finProdFinEquiv.symm j).2 * b (finProdFinEquiv.symm j).2 *
          c (finProdFinEquiv.symm j).2) := by ring
      _ = V ^ 2 := by rw [hvolume, hvolume]; ring
  refine ⟨k * k, a', b', c', Nat.mul_pos hk hk,
    mme_finite_MM_extraction_swap_double a b c hrestrict, hvol, ?_⟩
  simp_rw [hvol]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    Real.exp (2 * L) ≤ Real.exp (2 * Real.log (k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = ((k * k : ℕ) : ℝ) := by rw [two_mul, Real.exp_add, Real.exp_log hkr]; norm_cast


private theorem parentChild1_profiled0_intact0_fullChild1_behrend_log_loss_bound (N H : ℕ) (hH : H ≤ 4 ^ N) :
    100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      200 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
  have hp : H + 1 ≤ 4 ^ (N + 1) := by
    have hpos : 0 < 4 ^ N := by positivity
    rw [pow_succ]
    omega
  have hlog : Real.log ((H + 1 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
      (show ((H + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (N + 1) by exact_mod_cast hp)
    rw [Real.log_pow] at h
    have hfour : Real.log (4 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log 4 := h
      _ ≤ ((N + 1 : ℕ) : ℝ) * 4 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = _ := mul_comm _ _
  have hl0 : 0 ≤ Real.log ((H + 1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hs : Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt hl0,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity),
      Real.sqrt_nonneg (Real.log ((H + 1 : ℕ) : ℝ)),
      Real.sqrt_nonneg ((N + 1 : ℕ) : ℝ)]
  linarith


/-- The final square-root loss can be absorbed in any positive entropy
budget, uniformly across the six physical regions. -/
private theorem parentChild1_profiled0_intact0_fullChild1_child112_physical_clean_log_rate (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      let N := denominator * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r)
      let L := (2 * child112OuterCount r) * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r)
      let G := (denominator - 2 * child112OuterCount r) * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r)
      let p : ℝ := (child112OuterCount r : ℝ) / denominator
      ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
        0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
          (cyclicSymmetrization
            (CWCells.unbroken K 5 2
              ((2 * k) * (splitCount r parentChild1_profiled0_intact0_fullChild1_child112Split +
                splitCount r (complement (parent_total r) parentChild1_profiled0_intact0_fullChild1_child112Split)))
              (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
              (fun i _ w => (2 * k) * integerProfile i ⟨r, parentChild1_profiled0_intact0_fullChild1_child112Split⟩ w))) ∧
        (∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3) ∧
        ((2 * N : ℕ) : ℝ) *
          (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) ≤
          Real.log (copies : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_log_sqrt_loss_eventually_le_linear 0 200 0 delta hdelta)
  filter_upwards [parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_simultaneous_physical_extraction
    (delta / 6) (by positivity), eventually_ge_atTop n₀] with k hk hkn
  intro r
  have hs := parentChild1_profiled0_intact0_fullChild1_child112_physical_scale_pos r
  have hd : 0 < denominator := by decide
  have hlarge : n₀ ≤ denominator * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r) := by
    calc
      n₀ ≤ k := hkn
      _ ≤ k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r := by nlinarith
      _ ≤ denominator * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r) := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r) (show 1 ≤ denominator from hd)
  have hbudget := hn₀ _ hlarge
  have h := hk r
  dsimp only at h ⊢
  obtain ⟨A, H, hA, hH, hHbound, hlogA, hlogAH, hextract⟩ := h
  intro K _
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hrate⟩ := hextract K
  refine ⟨copies, a, b, c, hcopies, hrestrict, hvolume, ?_⟩
  change H ≤ 4 ^ (denominator * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r)) at hHbound
  have hloss := parentChild1_profiled0_intact0_fullChild1_behrend_log_loss_bound _ H hHbound
  change ((2 * (denominator * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r)) : ℕ) : ℝ) *
    (Real.log 2 * (mme_modern_entropyBits
      ![(child112OuterCount r : ℝ) / denominator,
        (child112OuterCount r : ℝ) / denominator,
        1 - 2 * ((child112OuterCount r : ℝ) / denominator)] + 2) - 3 * (delta / 6)) -
      100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤ Real.log (copies : ℝ) at hrate
  change H ≤ 4 ^ (denominator * (k * parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale r)) at hHbound
  simp only [zero_mul, zero_add, add_zero] at hbudget
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at hloss hbudget hrate ⊢
  nlinarith only [hrate, hloss, hbudget]


/-- All six released physical 112 cells attain their entropy and volume
rate after six-symmetrization, with any positive finite rate allowance. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_simultaneous_six_weight_rate
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      let s := (seed.region.getD r.val 0 *
        (splitWeight r (⟨![1, 1, 2], by decide⟩ : Split) +
          splitWeight r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))) * denominator)
      let N := denominator * (k * s)
      let L := (2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let G := (denominator - 2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let D := 4 * G + 2 * L
      let p : ℝ := ((((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2) : ℝ) / denominator
      ∀ (K : Type u) [Field K] (tau : ℝ),
        ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
          0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (sixSymmetrization
              (CWCells.unbroken K 5 2
                ((2 * k) * (splitCount r (⟨![1, 1, 2], by decide⟩ : Split) +
                  splitCount r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))))
                (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => (2 * k) * integerProfile i ⟨r, (⟨![1, 1, 2], by decide⟩ : Split)⟩ w))) ∧
          (∀ j, a j * b j * c j = 5 ^ (6 * D)) ∧
          Real.exp (((4 * N : ℕ) : ℝ) *
              (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
            ((6 * D : ℕ) : ℝ) * tau * Real.log 5) ≤
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [parentChild1_profiled0_intact0_fullChild1_child112_physical_clean_log_rate delta hdelta] with k hk
  intro r
  dsimp only
  intro K _ tau
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hlog⟩ := hk r K
  obtain ⟨count, a', b', c', hcount, hrestrict', hvolume', hweight⟩ :=
    parentChild1_profiled0_intact0_fullChild1_mme_cyclic_constant_volume_extraction_six_weight a b c hcopies
      hrestrict hvolume _ tau hlog
  dsimp only [parentChild1_profiled0_intact0_fullChild1_child112PhysicalScale, child112OuterCount, parentChild1_profiled0_intact0_fullChild1_child112Split] at hvolume' hweight
  refine ⟨count, a', b', c', hcount, hrestrict', ?_, ?_⟩
  · intro j
    rw [hvolume', ← pow_mul, ← pow_mul]
    congr 1
    ring
  · have hweight_eq (D : ℕ) :
        (((((5 ^ D) ^ 3) ^ 2 : ℕ) : ℝ) ^ tau) =
          Real.exp (((6 * D : ℕ) : ℝ) * tau * Real.log 5) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      push_cast
      simp only [Real.log_pow]
      congr 1
      ring
    rw [hweight_eq, ← Real.exp_add] at hweight
    convert hweight using 1
    congr 1
    push_cast
    ring


/-- Six-symmetrization commutes with finite tensor products, up to actual
mutual restrictions. -/
private theorem parentChild1_profiled0_intact0_fullChild1_mme_sixSymmetrization_kronFin_isomorphic
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kronFin n (fun i => sixSymmetrization (T i)))
      (sixSymmetrization (TensorObj.kronFin n T)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [mme_toQ_kronFin, sixSymmetrization,
    cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    ← TensorQ.permAut_toQ, map_prod, map_mul, Finset.prod_mul_distrib]


private theorem parentChild1_profiled0_intact0_fullChild1_six_product_exponential_extraction
    {K : Type u} [Field K] {n : ℕ} (T : Fin n → TensorObj K 3)
    (tau : ℝ) (rate : Fin n → ℝ)
    (hextract : ∀ i, ∃ (q : ℕ) (a b c : Fin q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (T i)) ∧
      Real.exp (rate i) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau)) :
    ∃ (q : ℕ) (a b c : Fin q → ℕ), 0 < q ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (TensorObj.kronFin n T)) ∧
      Real.exp (∑ i, rate i) ≤ ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨q, a, b, c, hrestrict, hweight⟩ :=
    mme_finite_MM_extractions_kronFin_tau_product
      (fun i => sixSymmetrization (T i)) tau (fun i => Real.exp (rate i))
      (fun i => (Real.exp_pos _).le) hextract
  have hweight' : Real.exp (∑ i, rate i) ≤
      ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
    simpa only [Real.exp_sum] using hweight
  have hq : 0 < q := by
    by_contra h
    have hz : q = 0 := by omega
    subst q
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hweight'
    exact (Real.exp_pos _).not_ge hweight'
  exact ⟨q, a, b, c, hq,
    hrestrict.trans (parentChild1_profiled0_intact0_fullChild1_mme_sixSymmetrization_kronFin_isomorphic T).1, hweight'⟩


/-- The six physical 112 regional cells can be extracted simultaneously
from their product, with the sum of their certified logarithmic rates. -/
private theorem parentChild1_profiled0_intact0_mme_released_116_child112_joint_product_weight_rate
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
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [parentChild1_profiled0_intact0_fullChild1_mme_released_116_child112_simultaneous_six_weight_rate delta hdelta]
    with k hk
  intro K _ tau
  apply parentChild1_profiled0_intact0_fullChild1_six_product_exponential_extraction
  intro r
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hweight⟩ := hk r K tau
  exact ⟨copies, a, b, c, hrestrict, hweight⟩



open MME MME.RecursiveYZ MME.Released116
set_option autoImplicit false

private def parentChild1_profiled0_intact0_fullChild2_boundarySplit (i : Fin 3) : Split :=
  if i = 0 then ⟨![0, 0, 4], by decide⟩
  else if i = 1 then ⟨![0, 1, 3], by decide⟩
  else ⟨![1, 0, 3], by decide⟩

private def parentChild1_profiled0_intact0_fullChild2_partitionCell : Fin 18 ⊕ Fin 6 → Cell 4 6 parent
  | .inl i => ⟨(finProdFinEquiv.symm i : Fin 6 × Fin 3).1,
      parentChild1_profiled0_intact0_fullChild2_boundarySplit (finProdFinEquiv.symm i : Fin 6 × Fin 3).2⟩
  | .inr r => ⟨r, ⟨![1, 1, 2], by change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i; decide⟩⟩

private theorem parentChild1_profiled0_intact0_fullChild2_cell_eq_iff (x y : Cell 4 6 parent) :
    x = y ↔ x.1 = y.1 ∧ ∀ i, (x.2.val i).val = (y.2.val i).val := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ ↦ rfl⟩
  · rcases x with ⟨r, x⟩
    rcases y with ⟨s, y⟩
    rintro ⟨hrs, hval⟩
    dsimp only at hrs hval
    subst s
    congr 1
    apply Subtype.ext
    funext i
    exact Fin.ext (hval i)

private theorem parentChild1_profiled0_intact0_fullChild2_partitionCell_bijective : Function.Bijective parentChild1_profiled0_intact0_fullChild2_partitionCell := by
  unfold Function.Bijective Function.Injective Function.Surjective
  simp only [parentChild1_profiled0_intact0_fullChild2_cell_eq_iff]
  decide +kernel

/-- The full released child index consists of eighteen boundary cells and
six interior 112 cells. The equivalence retains each physical cell once. -/
private theorem parentChild1_profiled0_intact0_fullChild2_mme_released_116_child_partition :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i; decide⟩⟩) := by
  refine ⟨Equiv.ofBijective parentChild1_profiled0_intact0_fullChild2_partitionCell parentChild1_profiled0_intact0_fullChild2_partitionCell_bijective, ?_, ?_⟩
  · change ∀ i : Fin 18, ∃ z : Fin 3, ((parentChild1_profiled0_intact0_fullChild2_partitionCell (.inl i)).2.val z).val = 0
    decide +kernel
  · intro r
    rfl



open MME BigOperators
set_option autoImplicit false

/-- A partition of the finite factor index gives an actual tensor
isomorphism to the Kronecker product of the two indexed subproducts. -/
private theorem parentChild1_profiled0_intact0_fullChild2_mme_kronFin_partition_isomorphic {K : Type u} [Field K] {a b : ℕ}
    (e : (Fin a ⊕ Fin b) ≃ Fin (a + b)) (T : Fin (a + b) → TensorObj K 3) :
    TensorObj.Isomorphic (TensorObj.kronFin (a + b) T)
      (TensorObj.kron
        (TensorObj.kronFin a (fun i ↦ T (e (.inl i))))
        (TensorObj.kronFin b (fun i ↦ T (e (.inr i))))) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [TensorQ.toQ_kron, mme_toQ_kronFin]
  rw [← Equiv.prod_comp e (fun i ↦ TensorQ.toQ (T i)), Fintype.prod_sum_type]


/-- The released full child tensor splits into its eighteen boundary factors
and six canonical 112 factors, independently of the original enumeration. -/
private theorem parentChild1_profiled0_intact0_fullChild2_mme_released_116_child_tensor_partition :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
        (T : Cell 4 6 parent → TensorObj K 3),
        TensorObj.Isomorphic (TensorObj.kronFin 24 (fun i ↦ T (d i)))
          (TensorObj.kron
            (TensorObj.kronFin 18 (fun i ↦ T (e (.inl i))))
            (TensorObj.kronFin 6 (fun r ↦ T ⟨r, ⟨![1, 1, 2], by
              change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
              decide⟩⟩))) := by
  obtain ⟨e, hb, hi⟩ := parentChild1_profiled0_intact0_fullChild2_mme_released_116_child_partition
  refine ⟨e, hb, hi, ?_⟩
  intro d K _ T
  have h := parentChild1_profiled0_intact0_fullChild2_mme_kronFin_partition_isomorphic (K := K) (e.trans d.symm)
    (fun i ↦ T (d i))
  simpa only [Equiv.trans_apply, Equiv.apply_symm_apply, hi] using h


open MME BigOperators
set_option autoImplicit false

private theorem parentChild1_profiled0_intact0_fullChild2_kron_restrict_for_tau_product
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hleft :
      P.le (TensorQ.toQ X * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y) :=
    P.mul_right _ _ hx _
  have hright :
      P.le (TensorQ.toQ X' * TensorQ.toQ Y)
        (TensorQ.toQ X' * TensorQ.toQ Y') := by
    simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X')
  exact P.le_trans _ _ _ hleft hright


private theorem parentChild1_profiled0_intact0_fullChild2_six_kron_iso {K : Type u} [Field K] (X Y : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.kron (sixSymmetrization X) (sixSymmetrization Y))
      (sixSymmetrization (TensorObj.kron X Y)) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [sixSymmetrization, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, ← TensorQ.permAut_toQ, map_mul]
  ring

/-- A square boundary extraction multiplies every interior matrix dimension
without changing the number of summands or losing exponential weight. -/
private theorem parentChild1_profiled0_intact0_fullChild2_mme_six_square_family_product_weight
    {K : Type u} [Field K] {X Y : TensorObj K 3} {q : ℕ}
    (M : ℕ) (a b c : Fin q → ℕ) (tau boundaryRate interiorRate : ℝ)
    (hboundary : TensorObj.Restrict (MMObj K M M M) (sixSymmetrization X))
    (hinterior : TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i))) (sixSymmetrization Y))
    (hboundaryWeight : Real.exp boundaryRate ≤ ((M * M * M : ℕ) : ℝ) ^ tau)
    (hinteriorWeight : Real.exp interiorRate ≤
      ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
      (sixSymmetrization (TensorObj.kron X Y)) ∧
    Real.exp (boundaryRate + interiorRate) ≤
      ∑ i, (((M * a i) * (M * b i) * (M * c i) : ℕ) : ℝ) ^ tau := by
  have hdist : TensorObj.Isomorphic
      (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
      (TensorObj.kron (MMObj K M M M)
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))) := by
    rw [← TensorQ.toQ_eq_iff, TensorQ.toQ_kron, TensorQ.toQ_bigAdd,
      TensorQ.toQ_bigAdd, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (TensorQ.toQ_eq_iff.mpr (MMObj_kron_iso (K := K)
      M M M (a i) (b i) (c i))).symm.trans (TensorQ.toQ_kron _ _)
  constructor
  · exact hdist.1.trans ((parentChild1_profiled0_intact0_fullChild2_kron_restrict_for_tau_product (by decide)
      hboundary hinterior).trans (parentChild1_profiled0_intact0_fullChild2_six_kron_iso X Y).1)
  · rw [Real.exp_add]
    have hmul := mul_le_mul hboundaryWeight hinteriorWeight
      (Real.exp_pos interiorRate).le (Real.rpow_nonneg (by positivity) tau)
    calc
      Real.exp boundaryRate * Real.exp interiorRate ≤
          ((M * M * M : ℕ) : ℝ) ^ tau *
            ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau := hmul
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        push_cast
        ring


/-- Boundary and interior extraction weights combine on the full released
child tensor, preserving the interior summands and every physical child factor. -/
private theorem parentChild1_profiled0_intact0_mme_released_116_full_child_weight_assembly :
    ∃ e : (Fin 18 ⊕ Fin 6) ≃ Cell 4 6 parent,
      (∀ i : Fin 18, ∃ z : Fin 3, ((e (.inl i)).2.val z).val = 0) ∧
      (∀ r : Fin 6, e (.inr r) = ⟨r, ⟨![1, 1, 2], by
        change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
        decide⟩⟩) ∧
      ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
        (T : Cell 4 6 parent → TensorObj K 3) (q M : ℕ)
        (a b c : Fin q → ℕ) (tau boundaryRate interiorRate : ℝ),
        TensorObj.Restrict (MMObj K M M M)
          (sixSymmetrization (TensorObj.kronFin 18 (fun i ↦ T (e (.inl i))))) →
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
          (sixSymmetrization (TensorObj.kronFin 6 (fun r ↦ T ⟨r, ⟨![1, 1, 2], by
            change _ ∧ ∀ i, _ ≤ (![1, 1, 6] : Fin 3 → ℕ) i
            decide⟩⟩))) →
        Real.exp boundaryRate ≤ ((M * M * M : ℕ) : ℝ) ^ tau →
        Real.exp interiorRate ≤ ∑ i, ((a i * b i * c i : ℕ) : ℝ) ^ tau →
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (M * a i) (M * b i) (M * c i)))
          (sixSymmetrization (TensorObj.kronFin 24 (fun i ↦ T (d i)))) ∧
        Real.exp (boundaryRate + interiorRate) ≤
          ∑ i, (((M * a i) * (M * b i) * (M * c i) : ℕ) : ℝ) ^ tau := by
  obtain ⟨e, hb, hi, hpartition⟩ := parentChild1_profiled0_intact0_fullChild2_mme_released_116_child_tensor_partition.{u}
  refine ⟨e, hb, hi, ?_⟩
  intro d K _ T q M a b c tau boundaryRate interiorRate hboundary hinterior hwB hwI
  obtain ⟨hextract, hweight⟩ := parentChild1_profiled0_intact0_fullChild2_mme_six_square_family_product_weight
    M a b c tau boundaryRate interiorRate hboundary hinterior hwB hwI
  exact ⟨hextract.trans (mme_sixSymmetrization_restrict (hpartition d K T).2), hweight⟩



/-- The full released child tensor has cofinal, positive-copy matrix
extractions attaining the sum of the boundary and interior entropy rates. -/
private theorem parentChild1_profiled0_mme_released_116_full_child_product_weight_rate
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
        ∀ (d : Fin 24 ≃ Cell 4 6 parent) (K : Type u) [Field K]
          (tau : ℝ), 0 ≤ tau →
        ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
            (sixSymmetrization (TensorObj.kronFin 24 (fun j ↦
              CWCells.unbroken K 5 2 ((2 * k) * mass (d j))
                (Equiv.refl _) (fun _ => Unit.unit)
                (fun _ i => ((d j).2.val i).val)
                (fun i _ w => (2 * k) * integerProfile i (d j) w)))) ∧
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
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  classical
  dsimp only
  obtain ⟨e, hb, hi, hassembly⟩ := parentChild1_profiled0_intact0_mme_released_116_full_child_weight_assembly.{u}
  choose z hz using hb
  obtain ⟨B, hmu, hboundary⟩ := parentChild1_profiled0_intact0_mme_released_116_boundary_product_weight_rate.{u}
    18 (fun r ↦ e (.inl r)) z hz delta hdelta
  refine ⟨e, z, B, hz, hi, hmu, ?_⟩
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hboundary
  filter_upwards [eventually_ge_atTop n₀,
    parentChild1_profiled0_intact0_mme_released_116_child112_joint_product_weight_rate.{u} delta hdelta]
    with k hkn hinterior
  obtain ⟨M, hM, hrestrictB, hweightB⟩ := hn₀ (2 * k) (by omega)
  intro d K _ tau htau
  obtain ⟨copies, a, b, c, hcopies, hrestrictI, hweightI⟩ := hinterior K tau
  have hshape (i : Fin 3) : ((![1, 1, 2] : Fin 3 → Fin 5) i).val =
      (![1, 1, 2] : Fin 3 → ℕ) i := by
    fin_cases i <;> rfl
  refine ⟨copies, (fun j ↦ M * a j), (fun j ↦ M * b j),
    (fun j ↦ M * c j), hcopies, ?_⟩
  exact hassembly d K
    (fun cell ↦ CWCells.unbroken K 5 2
      ((2 * k) * (splitCount cell.1 cell.2 +
        splitCount cell.1 (complement (parent_total cell.1) cell.2)))
      (Equiv.refl _) (fun _ => Unit.unit) (fun _ i => (cell.2.val i).val)
      (fun i _ w => (2 * k) * integerProfile i cell w))
    copies M a b c tau _ _ (hrestrictB K) (by simpa only [hshape] using hrestrictI)
    (hweightB tau htau) hweightI



open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells
open MME.CompleteSplit MME.TensorObj
set_option autoImplicit false

private theorem parentChild1_profiled0_intact1_full_cell_fiber {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (r : Fin R)
    (c : MME.RecursiveThinSplit.Split half (parent r)) :
    Fintype.card {p : Position n // fullCell htotal a p = ⟨r,c⟩} =
      MME.RecursiveThinSplit.count (a r) c +
      MME.RecursiveThinSplit.count (a r) (complement (htotal r) c) := by
  classical
  let e : {p : Position n // fullCell htotal a p = ⟨r,c⟩} ≃
      {p : Fin (n r) × Fin 2 //
        (if p.2 = 0 then a r p.1 else complement (htotal r) (a r p.1)) = c} := {
    toFun := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨(t,h), eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun p ↦ ⟨⟨r,p.val⟩, by
      change (⟨r,_⟩ : Cell half R parent) = ⟨r,c⟩
      rw [p.property]⟩
    left_inv := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro p; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  have hc (t : Fin (n r)) : complement (htotal r) (a r t) = c ↔
      a r t = complement (htotal r) c := by
    constructor
    · intro h
      simpa only [complement_complement] using congrArg (complement (htotal r)) h
    · intro h
      rw [h, complement_complement]
  simp only [show (1 : Fin 2) ≠ 0 by decide, 
    MME.RecursiveThinSplit.count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_add_distrib]
  simp only [ite_true, ite_false, hc]
  congr 1

/-- Exact address counts identify the sizes of the physical child fibers.
Their tensor product restricts from the intact reference tensor. -/
private theorem parentChild1_profiled0_mme_recursive_yz_reference_child_product_restrict
    {K : Type u} [Field K] {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (reference : Address half R parent n)
    (href : reference ∈ RecursiveXHash.target m)
    (ell L parts : ℕ) (positions : Fin L ≃ Position n)
    (d : Fin parts ≃ Cell half R parent)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) :
    Restrict (kronFin parts (fun j ↦
      unbroken K 5 ell
        (m (d j).1 (d j).2 + m (d j).1 (complement (htotal (d j).1) (d j).2))
        (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ ((d j).2.val i).val)
        (fun i _ ↦ mu i (d j))))
      (unbroken K 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu) := by
  classical
  have hcounts : ∀ r c, RecursiveThinSplit.count (reference r) c = m r c :=
    (Finset.mem_filter.mp href).2
  let D : Partition (fullCell htotal reference) := {
    parts := parts
    cells := d
    size := fun j ↦ m (d j).1 (d j).2 +
      m (d j).1 (complement (htotal (d j).1) (d j).2)
    fiber := fun j ↦ (Fintype.equivFinOfCardEq (by
      rw [parentChild1_profiled0_intact1_full_cell_fiber htotal reference (d j).1 (d j).2, hcounts, hcounts])).symm }
  exact mme_recursive_yz_actual_cell_product_restriction
    5 ell L positions (fullCell htotal reference) (fun cell i ↦ (cell.2.val i).val) mu D



/-- Every released reference address admits the combined boundary and interior
weight rate in its intact regional tensor at sufficiently large replication. -/
private theorem parentChild1_mme_released_116_intact_reference_weight_rate
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
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  classical
  dsimp only
  obtain ⟨e, z, B, hz, hi, hmu, hrate⟩ :=
    parentChild1_profiled0_mme_released_116_full_child_product_weight_rate.{u} delta hdelta
  refine ⟨e, z, B, hz, hi, hmu, ?_⟩
  filter_upwards [hrate] with k hk
  intro d L positions reference href K _ tau htau
  obtain ⟨copies, a, b, c, hcopies, hextract, hweight⟩ := hk d K tau htau
  refine ⟨copies, a, b, c, hcopies, ?_, hweight⟩
  have hgroup := parentChild1_profiled0_mme_recursive_yz_reference_child_product_restrict (K := K)
    parent_total (fun r c ↦ (2 * k) * splitCount r c) reference href
    2 L 24 positions d (fun i cell w ↦ (2 * k) * integerProfile i cell w)
  have hgroup' : TensorObj.Restrict
      (TensorObj.kronFin 24 (fun j ↦ CWCells.unbroken K 5 2
        ((2 * k) * (splitCount (d j).1 (d j).2 +
          splitCount (d j).1 (complement (parent_total (d j).1) (d j).2)))
        (Equiv.refl _) (fun _ ↦ Unit.unit) (fun _ i ↦ ((d j).2.val i).val)
        (fun i _ w ↦ (2 * k) * integerProfile i (d j) w)))
      (CWCells.unbroken K 5 2 L positions (fullCell parent_total reference)
        (fun cell i ↦ (cell.2.val i).val)
        (fun i cell w ↦ (2 * k) * integerProfile i cell w)) := by
    have hsize (a b : ℕ) (shape : Fin 3 → ℕ)
        (mu : Fin 3 → CompleteWord 2 → ℕ) :
        CWCells.unbroken K 5 2 ((2 * k) * (a + b)) (Equiv.refl _)
          (fun _ ↦ Unit.unit) (fun _ ↦ shape) (fun i _ ↦ mu i) =
        CWCells.unbroken K 5 2 ((2 * k) * a + (2 * k) * b) (Equiv.refl _)
          (fun _ ↦ Unit.unit) (fun _ ↦ shape) (fun i _ ↦ mu i) :=
      congrArg (fun t ↦ CWCells.unbroken K 5 2 t (Equiv.refl _)
        (fun _ ↦ Unit.unit) (fun _ ↦ shape) (fun i _ ↦ mu i)) (Nat.mul_add _ _ _)
    simp only [hsize]
    exact hgroup
  exact hextract.trans (mme_sixSymmetrization_restrict hgroup')



open MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ
open MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false

private theorem parentChild1_profiled1_tensor_cast {K : Type u} [Field K] {n m : ℕ} (h : n = m)
    (P : Predicate m) :
    tensor K (fun i (x : ProfiledCW.FineWord n) ↦ P i (fun j ↦ x (Fin.cast h.symm j))) =
      tensor K P := by
  subst m
  rfl

private theorem parentChild1_profiled1_split_cast {S : Type} {ell L N : ℕ} (p : Fin L ≃ S)
    (h : L * 2 ^ (ell - 1) = N) (x : WordIndex.{u} 5 ell L) :
    split p h (fun j ↦ fine x (Fin.cast h.symm j)) = CWCells.label 5 ell L p x := by
  funext s r
  simp [split, CWCells.label, fine]

/-- The intact reference tensor is contained in the profiled tensor of its
exact graded and useful output words, in the chosen flat coordinates. -/
private theorem parentChild1_mme_intact_reference_restrict_profiled_output
    {K : Type u} [Field K] {half R ell L N : ℕ}
    {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (reference : Address half R parent n) (positions : Fin L ≃ Position n)
    (length : L * 2 ^ (ell - 1) = N)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ) :
    Restrict
      (unbroken K 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu)
      (tensor K (fun i x ↦ Graded htotal i reference (split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (split positions length x))) := by
  classical
  let P : Predicate N := fun i x ↦ Graded htotal i reference (split positions length x) ∧
    Useful (fullCell htotal reference) (mu i) (split positions length x)
  let pull : Predicate (L * 2 ^ (ell - 1)) :=
    fun i x ↦ P i (fun j ↦ x (Fin.cast length.symm j))
  have hmono : Restrict
      (unbroken K 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu)
      (tensor K pull) := by
    apply mme_basis_projected_family_restrict (CWCells.source K 5 ell L)
      (CWCells.basis K 5 ell L) (fun i x ↦ pull i (fine x))
      (fun (_ : Fin 1) ↦ allowed 5 ell L positions (fullCell htotal reference)
        (fun cell i ↦ (cell.2.val i).val) mu)
    · intro j i x hx
      dsimp only [pull, P]
      rw [parentChild1_profiled1_split_cast]
      exact hx
    · intro x js _ _
      exact ⟨0, funext (fun i ↦ Fin.eq_zero (js i))⟩
  rw [show tensor K pull = tensor K P from parentChild1_profiled1_tensor_cast length P] at hmono
  exact hmono



/-- Every released reference address admits the combined boundary and interior
weight rate in its profiled output tensor at sufficiently large replication. -/
private theorem mme_released_116_profiled_output_weight_rate
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
        ∀ (d : Fin 24 ≃ Cell 4 6 parent) (L N : ℕ)
          (positions : Fin L ≃ Position (fun r : Fin 6 ↦ (2 * k) * regionalSize r))
          (length : L * 2 ^ (2 - 1) = N)
          (reference : Address 4 6 parent (fun r ↦ (2 * k) * regionalSize r)),
          reference ∈ RecursiveXHash.target (fun r c ↦ (2 * k) * splitCount r c) →
          ∀ (K : Type u) [Field K]
          (tau : ℝ), 0 ≤ tau →
        ∃ (copies : ℕ) (a b c : Fin copies → ℕ), 0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
            (sixSymmetrization (ProfiledCW.tensor K (fun i x ↦
              Graded parent_total i reference (ProfiledCW.split positions length x) ∧
              Useful (fullCell parent_total reference)
                (fun cell w ↦ (2 * k) * integerProfile i cell w)
                (ProfiledCW.split positions length x)))) ∧
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
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  classical
  dsimp only
  obtain ⟨e, z, B, hz, hi, hmu, hrate⟩ :=
    parentChild1_mme_released_116_intact_reference_weight_rate.{u} delta hdelta
  refine ⟨e, z, B, hz, hi, hmu, ?_⟩
  filter_upwards [hrate] with k hk
  intro d L N positions length reference href K _ tau htau
  obtain ⟨copies, a, b, c, hcopies, hextract, hweight⟩ :=
    hk d L positions reference href K tau htau
  refine ⟨copies, a, b, c, hcopies, ?_, hweight⟩
  exact hextract.trans (mme_sixSymmetrization_restrict
    (parentChild1_mme_intact_reference_restrict_profiled_output parent_total reference positions length
      (fun i cell w ↦ (2 * k) * integerProfile i cell w)))



open MME BigOperators
set_option autoImplicit false

/-- Repeating a tensor before six-symmetrization gives the sixth power of
its multiplicity, with no loss of copies. -/
private theorem mme_sixSymmetrization_repeated_isomorphic
    {K : Type u} [Field K] (p : ℕ) (T : TensorObj K 3) :
    TensorObj.Isomorphic
      (TensorObj.bigAdd (fun _ : Fin (p ^ 6) => sixSymmetrization T))
      (sixSymmetrization (TensorObj.bigAdd (fun _ : Fin p => T))) := by
  rw [← TensorQ.toQ_eq_iff]
  simp only [sixSymmetrization, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, TensorQ.toQ_bigAdd, ← TensorQ.permAut_toQ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    map_mul, map_natCast, Nat.cast_pow]
  ring

/-- A child extraction composes with a repeated parent extraction while
retaining all sixth-power copies created by symmetrization. -/
private theorem mme_six_repeated_extraction_compose
    {K : Type u} [Field K] {p : ℕ} {X Y Z : TensorObj K 3}
    (hparent : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin p => Y)) X)
    (hchild : TensorObj.Restrict Z (sixSymmetrization Y)) :
    TensorObj.Restrict (TensorObj.bigAdd (fun _ : Fin (p ^ 6) => Z))
      (sixSymmetrization X) := by
  exact (mme_bigAdd_mono_restrict (fun _ => hchild)).trans
    ((mme_sixSymmetrization_repeated_isomorphic p Y).1.trans
      (mme_sixSymmetrization_restrict hparent))


private theorem parentChild2_repeated_sum {A : Type*} [AddCommMonoid A] (p q : ℕ) (f : Fin q → A) :
    (∑ r : Fin (p * q), f (finProdFinEquiv.symm r).2) = p • ∑ j, f j := by
  calc
    _ = ∑ ij : Fin p × Fin q, f ij.2 := by
      symm
      apply Fintype.sum_equiv finProdFinEquiv
      intro ij
      rw [Equiv.symm_apply_apply]
    _ = _ := by simp [Fintype.sum_prod_type]

/-- Flattening the repeated child family retains the parent multiplicity
and multiplies the child's weight by its sixth power. -/
private theorem mme_six_repeated_matrix_family_weight
    {K : Type u} [Field K] {p q : ℕ} {X Y : TensorObj K 3}
    (a b c : Fin q → ℕ) (tau rate : ℝ)
    (hparent : TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin p => Y)) X)
    (hchild : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (sixSymmetrization Y))
    (hweight : Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun r : Fin (p ^ 6 * q) =>
        let j := (finProdFinEquiv.symm r).2
        MMObj K (a j) (b j) (c j))) (sixSymmetrization X) ∧
    (p : ℝ) ^ 6 * Real.exp rate ≤
      ∑ r : Fin (p ^ 6 * q),
        let j := (finProdFinEquiv.symm r).2
        ((a j * b j * c j : ℕ) : ℝ) ^ tau := by
  constructor
  · have hflatten : TensorObj.Isomorphic
        (TensorObj.bigAdd (fun r : Fin (p ^ 6 * q) =>
          let j := (finProdFinEquiv.symm r).2
          MMObj K (a j) (b j) (c j)))
        (TensorObj.bigAdd (fun _ : Fin (p ^ 6) =>
          TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))) := by
      rw [← TensorQ.toQ_eq_iff]
      simp only [TensorQ.toQ_bigAdd]
      rw [parentChild2_repeated_sum (p ^ 6) q (fun j => TensorQ.toQ (MMObj K (a j) (b j) (c j)))]
      simp
    exact hflatten.1.trans (mme_six_repeated_extraction_compose hparent hchild)
  · dsimp only
    rw [parentChild2_repeated_sum (p ^ 6) q (fun j => ((a j * b j * c j : ℕ) : ℝ) ^ tau),
      nsmul_eq_mul, Nat.cast_pow]
    exact mul_le_mul_of_nonneg_left hweight (by positivity)



/-- Cofinal released parent windows admit actual matrix families with the
combined child rate and the full sixth power of the surviving parent copies. -/
theorem solution
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
              ((a j * b j * c j : ℕ) : ℝ) ^ tau := by
  classical
  dsimp only
  obtain ⟨e, z, B, hz, hi, hmu, hchild⟩ :=
    mme_released_116_profiled_output_weight_rate.{u} delta hdelta
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hchild
  obtain ⟨eps0, heps0, hparent⟩ :=
    mme_released_116_cofinal_even_tensor_restriction_positive_copies (KField := KField)
  refine ⟨e, z, B, hz, hi, hmu, eps0, heps0, ?_⟩
  intro eps heps hepsle
  obtain ⟨d, hd, hcofinal⟩ := hparent eps heps hepsle
  refine ⟨d, hd, ?_⟩
  intro K
  obtain ⟨k, hK, hk, heven, positions, reference, href, E, hpos,
    hcount, hexponent, hrepair, houtput, hrestrict, hcopies⟩ :=
    hcofinal (max K (2 * K0))
  obtain ⟨t, ht⟩ := heven
  have hkt : k = 2 * t := by omega
  have ht0 : K0 ≤ t := by have := le_max_right K (2 * K0); omega
  clear ht
  subst k
  refine ⟨2 * t, (le_max_left K (2 * K0)).trans hK, hk,
    ⟨t, by omega⟩, positions, reference, href, E, hpos,
    hcount, hexponent, hrepair, houtput, hrestrict, hcopies, t, rfl, ?_⟩
  obtain ⟨copies, a, b, c, hpositive, hextract, hweight⟩ :=
    hK0 t ht0 (finSumFinEquiv.symm.trans e)
      (((2 * t) * denominator ^ 4) * 2) (((2 * t) * denominator ^ 4) * 4)
      positions (by omega) reference href KField tau htau
  have hchildOutput : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj KField (a j) (b j) (c j)))
      (sixSymmetrization (tensor KField E.output)) := by
    rw [houtput]
    exact hextract
  exact ⟨copies, a, b, c, hpositive,
    mme_six_repeated_matrix_family_weight a b c tau _ hrestrict hchildOutput hweight⟩


#print axioms solution
