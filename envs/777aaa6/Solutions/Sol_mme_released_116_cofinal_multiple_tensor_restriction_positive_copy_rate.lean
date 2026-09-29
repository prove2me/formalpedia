-- Prove2me | solution 1 for mme_released_116_cofinal_multiple_tensor_restriction_positive_copy_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T02:24:54.701758+00:00
-- url     : https://prove2.me/submissions/80c59635-42e0-4607-acca-8d0834ab1aa5

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

namespace RateBound

namespace CoarseBound

open BigOperators MME MME.RegionRate MME.RecursiveThinSplit
set_option autoImplicit false

/-- A tangent bound for the logarithm turns an atom-size bound into an entropy bound. -/
private theorem mme_entropy_lower_of_scaled_atom_bound {W : Type*} [Fintype W]
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

private theorem mass_entropy_lower {W : Type*} [Fintype W]
    (x : W → ℝ) (s a b : ℝ) (hs : 0 < s) (ha : 0 < a) (hx : ∀ w, 0 ≤ x w)
    (hmass : ∑ w, x w = s) (hbound : ∀ w, x w ≤ b * s) :
    s * (Real.log a + 1 - a * b) ≤ massEntropy x := by
  rw [(mme_regional_mass_entropy_algebra (C := Unit) (W := W)).2.1 x
    (by rw [hmass]; exact hs.ne'), hmass]
  apply mul_le_mul_of_nonneg_left _ hs.le
  apply mme_entropy_lower_of_scaled_atom_bound _ _ _ ha
  · intro w; exact div_nonneg (hx w) hs.le
  · rw [← Finset.sum_div, hmass, div_self hs.ne']
  · intro w; exact (div_le_iff₀ hs).2 (hbound w)

private abbrev Split116 := Split 4 ![1, 1, 6]
private def c004 : Split116 := ⟨![0, 0, 4], by decide⟩
private def c013 : Split116 := ⟨![0, 1, 3], by decide⟩
private def c103 : Split116 := ⟨![1, 0, 3], by decide⟩
private def c112 : Split116 := ⟨![1, 1, 2], by decide⟩

private theorem split_univ : (Finset.univ : Finset Split116) = {c004, c013, c103, c112} := by
  decide

private def xCounts (r : Fin 6) (j : Fin 5) : ℕ :=
  if j = 0 then Released116.splitCount r c004 + Released116.splitCount r c013
  else if j = 1 then Released116.splitCount r c103 + Released116.splitCount r c112
  else 0

private theorem x_counts_bound : ∀ (r : Fin 6) (j : Fin 5),
    1000000 * xCounts r j ≤ 500001 * Released116.regionalSize r := by
  decide +kernel

private theorem x_counts_mass : ∀ r : Fin 6,
    ∑ j : Fin 5, xCounts r j = Released116.regionalSize r := by
  decide +kernel

private theorem x_counts_eq (r : Fin 6) (j : Fin 5) :
    marginalCounts Released116.splitCount 0 r j = xCounts r j := by
  classical
  unfold marginalCounts
  change (∑ c : {c : Split116 // c.val 0 = j}, Released116.splitCount r c.val) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c : Split116 => c.val 0 = j))
    (fun c => by simp) (Released116.splitCount r), Finset.sum_filter, split_univ]
  fin_cases j <;> norm_num [c004, c013, c103, c112, xCounts, add_assoc]

/-- The released X-coordinate entropy is at least 0.69 per parent occurrence.
The proof uses exact integer histogram bounds and the elementary logarithm inequality. -/
private theorem mme_released_116_coarse_rate_lower :
    (69 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      coarsePotential Released116.splitCount 0 := by
  unfold coarsePotential
  simp only [x_counts_eq]
  have hr (r : Fin 6) :
      (Released116.regionalSize r : ℝ) * (Real.log 2 + 1 - 2 * (500001 / 1000000 : ℝ)) ≤
        massEntropy (fun j => (xCounts r j : ℝ)) := by
    apply mass_entropy_lower
    · exact_mod_cast (mme_released_116_regional_split_mass r).1
    · norm_num
    · intro j; exact Nat.cast_nonneg _
    · exact_mod_cast x_counts_mass r
    · intro j
      have h : (1000000 : ℝ) * xCounts r j ≤ 500001 * Released116.regionalSize r := by
        exact_mod_cast x_counts_bound r j
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
private theorem mme_entropy_lower_of_scaled_atom_bound {W : Type*} [Fintype W]
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

private abbrev Word := CompleteSplit.CompleteWord 2
private abbrev Split116 := Split 4 ![1, 1, 6]
private def c004 : Split116 := ⟨![0, 0, 4], by decide⟩
private def c013 : Split116 := ⟨![0, 1, 3], by decide⟩
private def c103 : Split116 := ⟨![1, 0, 3], by decide⟩
private def c112 : Split116 := ⟨![1, 1, 2], by decide⟩

private theorem split_univ : (Finset.univ : Finset Split116) = {c004, c013, c103, c112} := by
  decide

private theorem split_sum (f : Split116 → ℝ) :
    ∑ c, f c = f c004 + f c013 + f c103 + f c112 := by
  rw [split_univ]
  norm_num [c004, c013, c103, c112, add_assoc]

private def frequencyQ (i : Fin 3) (r : Fin 6) (c : Split116) (w : Word) : ℚ :=
  (Released116.integerProfile i ⟨r, c⟩ w : ℚ) /
    (∑ v : Word, Released116.integerProfile i ⟨r, c⟩ v : ℕ)

private def mixtureQ (i : Fin 3) (r : Fin 6) (w : Fin 2 → Word) : ℚ :=
  ((Released116.splitCount r c004 : ℚ) * frequencyQ i r c004 (w 0) * frequencyQ i r c112 (w 1) +
   (Released116.splitCount r c013 : ℚ) * frequencyQ i r c013 (w 0) * frequencyQ i r c103 (w 1) +
   (Released116.splitCount r c103 : ℚ) * frequencyQ i r c103 (w 0) * frequencyQ i r c013 (w 1) +
   (Released116.splitCount r c112 : ℚ) * frequencyQ i r c112 (w 0) * frequencyQ i r c004 (w 1)) /
    Released116.regionalSize r

private theorem frequencyQ_cast (i : Fin 3) (r : Fin 6) (c : Split116) (w : Word) :
    (frequencyQ i r c w : ℝ) = RegionRealization.cellFrequency
      (Released116.integerProfile i) ⟨r, c⟩ w := by
  simp [frequencyQ, RegionRealization.cellFrequency]

private theorem mixtureQ_cast (i : Fin 3) (r : Fin 6) (w : Fin 2 → Word) :
    (mixtureQ i r w : ℝ) = RegionRealization.parentMixture Released116.parent_total
      Released116.regionalSize Released116.splitCount (Released116.integerProfile i) r w := by
  unfold RegionRealization.parentMixture
  change _ = (∑ c : Split116, (Released116.splitCount r c : ℝ) *
    RegionRealization.cellFrequency (Released116.integerProfile i) ⟨r, c⟩ (w 0) *
    RegionRealization.cellFrequency (Released116.integerProfile i)
      ⟨r, RecursiveYZ.complement (Released116.parent_total r) c⟩ (w 1)) / _
  rw [split_sum]
  have h004 : RecursiveYZ.complement (Released116.parent_total r) c004 = c112 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  have h013 : RecursiveYZ.complement (Released116.parent_total r) c013 = c103 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  have h103 : RecursiveYZ.complement (Released116.parent_total r) c103 = c013 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  have h112 : RecursiveYZ.complement (Released116.parent_total r) c112 = c004 := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j <;> rfl
  simp only [mixtureQ, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
    frequencyQ_cast, h004, h013, h103, h112]

private theorem mixtureQ_y_bounds : ∀ (r : Fin 6) (w : Fin 2 → Word),
    0 ≤ mixtureQ 1 r w ∧ mixtureQ 1 r w ≤ 250001 / 1000000 := by
  decide +kernel

private theorem mixtureQ_y_mass : ∀ r : Fin 6, ∑ w : Fin 2 → Word, mixtureQ 1 r w = 1 := by
  decide +kernel

private theorem mixtureQ_z_bounds : ∀ (r : Fin 6) (w : Fin 2 → Word),
    0 ≤ mixtureQ 2 r w ∧ mixtureQ 2 r w ≤ 193 / 1000 := by
  decide +kernel

private theorem mixtureQ_z_mass : ∀ r : Fin 6, ∑ w : Fin 2 → Word, mixtureQ 2 r w = 1 := by
  decide +kernel

private theorem parent_lower (i : Fin 3) (b : ℚ) (L : ℝ)
    (hbound : ∀ (r : Fin 6) (w : Fin 2 → Word), 0 ≤ mixtureQ i r w ∧ mixtureQ i r w ≤ b)
    (hmass : ∀ r : Fin 6, ∑ w : Fin 2 → Word, mixtureQ i r w = 1)
    (hlog : L ≤ Real.log 4 + 1 - 4 * (b : ℝ)) :
    L * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      parentPotential Released116.parent_total Released116.regionalSize
        Released116.splitCount (Released116.integerProfile i) := by
  have hr (r : Fin 6) :
      L ≤ entropy (RegionRealization.parentMixture Released116.parent_total
        Released116.regionalSize Released116.splitCount (Released116.integerProfile i) r) := by
    apply hlog.trans
    apply mme_entropy_lower_of_scaled_atom_bound _ 4 (b : ℝ) (by norm_num)
    · intro w
      rw [← mixtureQ_cast]
      exact_mod_cast (hbound r w).1
    · simp_rw [← mixtureQ_cast]
      exact_mod_cast hmass r
    · intro w
      rw [← mixtureQ_cast]
      exact_mod_cast (hbound r w).2
  have h := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hr r) (Nat.cast_nonneg (Released116.regionalSize r)))
  rw [← Finset.sum_mul, ← Nat.cast_sum] at h
  simpa only [parentPotential, mul_comm L] using h

private theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  exact h

/-- The actual released Y parent mixtures have at least 1.38 natural-log entropy
per parent occurrence, certified from their exact rational atoms. -/
private theorem mme_released_116_parent_y_entropy_lower :
    (138 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      parentPotential Released116.parent_total Released116.regionalSize
        Released116.splitCount (Released116.integerProfile 1) := by
  apply parent_lower 1 (250001 / 1000000) _ mixtureQ_y_bounds mixtureQ_y_mass
  rw [log_four]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have := Real.log_two_gt_d9
  linarith

/-- The actual released Z parent mixtures have at least 1.6 natural-log entropy
per parent occurrence, certified from their exact rational atoms. -/
private theorem mme_released_116_parent_z_entropy_lower :
    (160 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      parentPotential Released116.parent_total Released116.regionalSize
        Released116.splitCount (Released116.integerProfile 2) := by
  apply parent_lower 2 (193 / 1000) _ mixtureQ_z_bounds mixtureQ_z_mass
  rw [log_four]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have := Real.log_two_gt_d9
  linarith


end ParentBound

namespace CompatibilityBound

open BigOperators MME.RegionRate
set_option autoImplicit false

/-- A probability distribution supported on at most k atoms has entropy at most log k. -/
private theorem mme_entropy_upper_of_support_card {W : Type*} [Fintype W]
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
private theorem mme_mass_entropy_upper_of_support_card {W : Type*} [Fintype W]
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
    apply mme_entropy_upper_of_support_card _ S k hk
    · intro w; positivity
    · rw [← Finset.sum_div, ← Nat.cast_sum, div_self (by exact_mod_cast hz)]
    · intro w hw; simp [hsupp w hw]
    · exact hcard


private abbrev Word := MME.CompleteSplit.CompleteWord 2
private def gradeSupport (j : Fin 5) : Finset Word :=
  Finset.univ.filter (fun w => ∑ h, (w h).val = j.val)

private theorem grade_card : ∀ j : Fin 5,
    (gradeSupport j).card ≤ 2 ^ j.val ∧ (gradeSupport j).card ≤ 2 ^ (4 - j.val) := by
  decide +kernel

private theorem grade_entropy_upper (mu : Word → ℕ) (j : Fin 5)
    (hsupp : ∀ w, 0 < mu w → ∑ h, (w h).val = j.val) (d : ℕ)
    (hcard : (gradeSupport j).card ≤ 2 ^ d) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * d * Real.log 2 := by
  have h := mme_mass_entropy_upper_of_support_card mu (gradeSupport j) (2 ^ d)
    (by positivity) (fun w hw => by
      by_contra hn
      have hg := hsupp w (Nat.pos_of_ne_zero hn)
      exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩)) hcard
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, mul_assoc] using h

/-- A two-symbol child histogram of grade j has at most 2^j possible words. -/
private theorem mme_complete_word_two_low_grade_entropy_upper
    (mu : MME.CompleteSplit.CompleteWord 2 → ℕ) (j : Fin 5)
    (hsupp : ∀ w, 0 < mu w → ∑ h, (w h).val = j.val) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * j.val * Real.log 2 := by
  exact grade_entropy_upper mu j hsupp j.val (grade_card j).1

/-- Reversing the word grades gives the sharper bound for high-grade children. -/
private theorem mme_complete_word_two_high_grade_entropy_upper
    (mu : MME.CompleteSplit.CompleteWord 2 → ℕ) (j : Fin 5)
    (hsupp : ∀ w, 0 < mu w → ∑ h, (w h).val = j.val) :
    massEntropy (fun w => (mu w : ℝ)) ≤ ((∑ w, mu w : ℕ) : ℝ) * (4 - j.val : ℕ) * Real.log 2 := by
  exact grade_entropy_upper mu j hsupp (4 - j.val) (grade_card j).2

open MME.RecursiveYZ
open scoped Classical

private theorem part_weighted_count {C W G : Type*} [Fintype C] [Fintype G]
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

private theorem part_weighted_mass {C W G : Type*} [Fintype C] [Fintype G] [Fintype W]
    (boundary : C → Prop) (group : C → G) (mu : C → W → ℕ) (d : G → ℕ) :
    ∑ s : {c : C // boundary c} ⊕ G,
      (∑ w, partCount boundary group mu s w) * (s.elim (fun c => d (group c.val)) d) =
        ∑ c, (∑ w, mu c w) * d (group c) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [part_weighted_count]
  rw [Finset.sum_comm]

open MME

private abbrev Parts (i : Fin 2) :=
  {c : Cell 4 6 Released116.parent // yzBoundary i c} ⊕ (Fin 6 × Fin 5)

private def partGrade (i : Fin 2) (s : Parts i) : Fin 5 :=
  s.elim (fun c => c.val.2.val (yzMode i)) Prod.snd

private theorem part_support (i : Fin 2) (s : Parts i) (w : Word)
    (h : 0 < partCount (yzBoundary i) (modeGroup (yzMode i))
      (Released116.integerProfile (yzMode i)) s w) :
    ∑ a, (w a).val = (partGrade i s).val := by
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

private theorem released_weighted_y_mass :
    ∑ c : Cell 4 6 Released116.parent,
      (∑ w, Released116.integerProfile 1 c w) * (modeGroup 1 c).2.val =
        ∑ r, Released116.regionalSize r := by
  decide +kernel

private theorem released_weighted_z_mass :
    ∑ c : Cell 4 6 Released116.parent,
      (∑ w, Released116.integerProfile 2 c w) * (4 - (modeGroup 2 c).2.val) =
        2 * ∑ r, Released116.regionalSize r := by
  decide +kernel

/-- The compatibility partition retains Y grades, whose total is one per parent. -/
private theorem mme_released_116_compatibility_y_entropy_upper :
    compatibilityPotential 0 (Released116.integerProfile 1) ≤
      ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) * Real.log 2 := by
  unfold compatibilityPotential
  rw [(mme_regional_mass_entropy_algebra (C := Parts 0) (W := Word)).2.2]
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    mme_complete_word_two_low_grade_entropy_upper
      (partCount (yzBoundary 0) (modeGroup (yzMode 0))
        (Released116.integerProfile (yzMode 0)) s)
      (partGrade 0 s) (part_support 0 s))
  refine h.trans_eq ?_
  rw [← Finset.sum_mul]
  have hm := part_weighted_mass (yzBoundary (half := 4) (parent := Released116.parent) 0)
    (modeGroup (yzMode 0)) (Released116.integerProfile (yzMode 0)) (fun g => g.2.val)
  have he (s : Parts 0) :
      s.elim (fun c => (modeGroup (yzMode 0) c.val).2.val) (fun g => g.2.val) =
        (partGrade 0 s).val := by cases s <;> rfl
  simp only [he] at hm
  have ht : (∑ s : Parts 0, (∑ w, partCount (yzBoundary 0) (modeGroup (yzMode 0))
    (Released116.integerProfile (yzMode 0)) s w) * (partGrade 0 s).val) =
      ∑ r, Released116.regionalSize r := hm.trans released_weighted_y_mass
  congr 1
  exact_mod_cast ht

/-- The complementary Z grade totals two per parent, bounding compatibility entropy. -/
private theorem mme_released_116_compatibility_z_entropy_upper :
    compatibilityPotential 1 (Released116.integerProfile 2) ≤
      (2 * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ)) * Real.log 2 := by
  unfold compatibilityPotential
  rw [(mme_regional_mass_entropy_algebra (C := Parts 1) (W := Word)).2.2]
  have h := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    mme_complete_word_two_high_grade_entropy_upper
      (partCount (yzBoundary 1) (modeGroup (yzMode 1))
        (Released116.integerProfile (yzMode 1)) s)
      (partGrade 1 s) (part_support 1 s))
  refine h.trans_eq ?_
  rw [← Finset.sum_mul]
  have hm := part_weighted_mass (yzBoundary (half := 4) (parent := Released116.parent) 1)
    (modeGroup (yzMode 1)) (Released116.integerProfile (yzMode 1)) (fun g => 4 - g.2.val)
  have he (s : Parts 1) :
      s.elim (fun c => 4 - (modeGroup (yzMode 1) c.val).2.val) (fun g => 4 - g.2.val) =
        4 - (partGrade 1 s).val := by cases s <;> rfl
  simp only [he] at hm
  have ht : (∑ s : Parts 1, (∑ w, partCount (yzBoundary 1) (modeGroup (yzMode 1))
    (Released116.integerProfile (yzMode 1)) s w) * (4 - (partGrade 1 s).val)) =
      2 * ∑ r, Released116.regionalSize r := hm.trans released_weighted_z_mass
  congr 1
  exact_mod_cast ht


end CompatibilityBound

namespace PenaltyBound

open BigOperators MME MME.RecursiveThinSplit
set_option autoImplicit false

private abbrev Split116 := Split 4 ![1, 1, 6]
private def c004 : Split116 := ⟨![0, 0, 4], by decide⟩
private def c013 : Split116 := ⟨![0, 1, 3], by decide⟩
private def c103 : Split116 := ⟨![1, 0, 3], by decide⟩
private def c112 : Split116 := ⟨![1, 1, 2], by decide⟩

private theorem split_univ : (Finset.univ : Finset Split116) = {c004, c013, c103, c112} := by
  decide

private theorem split_sum (f : Split116 → ℝ) :
    ∑ c, f c = f c004 + f c013 + f c103 + f c112 := by
  rw [split_univ]
  norm_num [c004, c013, c103, c112, add_assoc]

private theorem marginal_sum (f : Split116 → ℝ) (i : Fin 3) (j : Fin 5) :
    mme_modern_marginal (fun c : Split116 => c.val i) f j =
      ∑ c, if c.val i = j then f c else 0 := by
  unfold mme_modern_marginal
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c : Split116 => c.val i = j))
    (fun c => by simp) f, Finset.sum_filter]

/-- The three coordinate marginals determine a distribution on the four
splits of the (1,1,6) component. The extreme third-coordinate entries recover
004 and 112; the first two marginals then recover 103 and 013. -/
private theorem mme_116_split_marginals_injective (alpha rho : Split 4 ![1, 1, 6] → ℝ)
    (h : ∀ (i : Fin 3) (j : Fin 5),
      mme_modern_marginal (fun c : Split 4 ![1, 1, 6] => c.val i) rho j =
        mme_modern_marginal (fun c : Split 4 ![1, 1, 6] => c.val i) alpha j) :
    rho = alpha := by
  have h004 := h 2 4
  have h112 := h 2 2
  have h103 := h 0 1
  have h013 := h 1 1
  simp only [marginal_sum, split_sum] at h004 h112 h103 h013
  change rho c004 + 0 + 0 + 0 = alpha c004 + 0 + 0 + 0 at h004
  change 0 + 0 + 0 + rho c112 = 0 + 0 + 0 + alpha c112 at h112
  change 0 + 0 + rho c103 + rho c112 = 0 + 0 + alpha c103 + alpha c112 at h103
  change 0 + rho c013 + 0 + rho c112 = 0 + alpha c013 + 0 + alpha c112 at h013
  simp only [zero_add, add_zero] at h004 h112 h103 h013
  funext c
  have hc : c ∈ ({c004, c013, c103, c112} : Finset Split116) := by
    rw [← split_univ]
    exact Finset.mem_univ c
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> linarith

/-- Every probability distribution on the splits of (1,1,6) has zero
maximum-entropy penalty because its coordinate marginals fix it uniquely. -/
private theorem mme_116_split_entropy_penalty_zero (alpha : Split 4 ![1, 1, 6] → ℝ)
    (hnonneg : ∀ c, 0 ≤ alpha c) (hmass : ∑ c, alpha c = 1) :
    entropyPenalty alpha = 0 := by
  have hset : SameMarginalDistributions alpha = {alpha} := by
    ext rho
    constructor
    · intro h
      exact Set.mem_singleton_iff.mpr (mme_116_split_marginals_injective alpha rho h.2.2)
    · rintro rfl
      exact ⟨hnonneg, hmass, fun _ _ => rfl⟩
  simp [entropyPenalty, hset]


open scoped Classical

/-- The maximum-entropy penalty vanishes in each of the six released regions. -/
private theorem mme_released_116_regional_entropy_penalty_zero (r : Fin 6) :
    entropyPenalty (fun c : Released116.Split =>
      (Released116.splitCount r c : ℝ) / Released116.regionalSize r) = 0 := by
  apply mme_116_split_entropy_penalty_zero
  · intro c
    positivity
  · have hm := (mme_released_116_regional_split_mass r).2
    change (∑ c : Split 4 ![1, 1, 6], Released116.splitCount r c) = _ at hm
    rw [← Finset.sum_div, ← Nat.cast_sum, hm]
    exact div_self (by exact_mod_cast (mme_released_116_regional_split_mass r).1.ne')

/-- The released (1,1,6) regional rate has no aggregate entropy-penalty term. -/
private theorem mme_released_116_penalty_potential_zero :
    RegionRate.penaltyPotential Released116.regionalSize Released116.splitCount = 0 := by
  simp [RegionRate.penaltyPotential, mme_released_116_regional_entropy_penalty_zero]


end PenaltyBound

open BigOperators MME MME.RegionRate
set_option autoImplicit false

/-- The released (1,1,6) regional rate is at least 0.2 per parent occurrence.
This combines certified entropy bounds for all three coordinates, including
both compatibility subtractions and the vanishing split entropy penalty. -/
private theorem mme_released_116_regional_rate_lower :
    (1 / 5 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      regionalRate Released116.parent_total Released116.regionalSize
        Released116.splitCount Released116.integerProfile := by
  have hx : (69 / 100 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      coarsePotential (half := 4) (parent := Released116.parent) Released116.splitCount 0 :=
    CoarseBound.mme_released_116_coarse_rate_lower
  have hy := ParentBound.mme_released_116_parent_y_entropy_lower
  have hz := ParentBound.mme_released_116_parent_z_entropy_lower
  have hcy := CompatibilityBound.mme_released_116_compatibility_y_entropy_upper
  have hcz := CompatibilityBound.mme_released_116_compatibility_z_entropy_upper
  have hn : (0 : ℝ) ≤ ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hl : Real.log 2 ≤ (7 / 10 : ℝ) := le_of_lt (Real.log_two_lt_d9.trans (by norm_num))
  have hnl := mul_le_mul_of_nonneg_left hl hn
  have hpen : penaltyPotential (half := 4) (parent := Released116.parent)
      Released116.regionalSize Released116.splitCount = 0 :=
    PenaltyBound.mme_released_116_penalty_potential_zero
  unfold regionalRate
  rw [hpen, sub_zero]
  refine le_min ?_ (le_min ?_ ?_) <;> nlinarith

/-- The exact released profile has a strictly positive regional entropy rate. -/
private theorem mme_released_116_regional_rate_positive :
    0 < regionalRate Released116.parent_total Released116.regionalSize
      Released116.splitCount Released116.integerProfile := by
  have hn : 0 < ∑ r : Fin 6, Released116.regionalSize r := by decide +kernel
  have hn' : (0 : ℝ) < ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) := by
    exact_mod_cast hn
  exact lt_of_lt_of_le (mul_pos (by norm_num) hn') mme_released_116_regional_rate_lower


/-- A fixed positive tolerance preserves a quantitative entropy margin for every
smaller nonnegative tolerance in the actual released profile. -/
private theorem mme_released_116_small_tolerance_rate_lower :
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
  have hr := mme_released_116_regional_rate_lower
  linarith


end RateBound

namespace AsymptoticBound

open scoped Classical
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

/-- Replicating every occurrence preserves each normalized child profile. -/
private theorem mme_cell_frequency_scale
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [cellFrequency, ← Finset.mul_sum, Nat.cast_mul]
  exact mul_div_mul_left _ _ hk'

/-- Uniform replication preserves the regional parent-mixture centers. -/
private theorem mme_parent_mixture_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (k : ℕ) (hk : 0 < k) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c v => k * mu c v) r w = parentMixture htotal n m mu r w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [parentMixture, mme_cell_frequency_scale mu k hk, Nat.cast_mul,
    mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hk'


open MME.RegionRate

private theorem mass_entropy_scale {W : Type*} [Fintype W] (k : ℕ) (x : W → ℕ) :
    massEntropy (fun w => ((k * x w : ℕ) : ℝ)) =
      (k : ℝ) * massEntropy (fun w => (x w : ℝ)) := by
  simpa only [Nat.cast_mul] using
    (mme_regional_mass_entropy_algebra (C := Unit) (W := W)).1 (k : ℝ)
      (fun w => (x w : ℝ))

private theorem potential_scale {C W : Type*} [Fintype C] [Fintype W]
    (k : ℕ) (mu : C → W → ℕ) :
    potential (fun c w => k * mu c w) = (k : ℝ) * potential mu := by
  rw [(mme_regional_mass_entropy_algebra (C := C) (W := W)).2.2,
    (mme_regional_mass_entropy_algebra (C := C) (W := W)).2.2,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => mass_entropy_scale k (mu c))

private theorem part_count_scale {C W G : Type*} [Fintype C]
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
private theorem mme_regional_joint_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (k : ℕ) :
    jointPotential (fun r c => k * m r c) = (k : ℝ) * jointPotential m := by
  simp only [jointPotential, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => mass_entropy_scale k (m r))

private theorem coarse_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (k : ℕ) (i : Fin 3) :
    coarsePotential (fun r c => k * m r c) i = (k : ℝ) * coarsePotential m i := by
  simp only [coarsePotential, marginalCounts, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun r _ => mass_entropy_scale k _)

private theorem penalty_potential_scale {half R : ℕ}
    {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (k : ℕ) (hk : 0 < k) :
    penaltyPotential (fun r => k * n r) (fun r c => k * m r c) =
      (k : ℝ) * penaltyPotential n m := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [penaltyPotential, Nat.cast_mul, mul_div_mul_left _ _ hk',
    mul_assoc, Finset.mul_sum]

private theorem parent_potential_scale {half R : ℕ} {W : Type*} [Fintype W]
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
    exact mme_parent_mixture_scale htotal n m mu k hk r w
  simp only [parentPotential, heq, Nat.cast_mul, mul_assoc, Finset.mul_sum]

private theorem compatibility_potential_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ} (i : Fin 2)
    (mu : Cell half R parent → W → ℕ) (k : ℕ) :
    compatibilityPotential i (fun c w => k * mu c w) =
      (k : ℝ) * compatibilityPotential i mu := by
  simp only [compatibilityPotential]
  have heq : partCount (yzBoundary i) (modeGroup (yzMode i)) (fun c w => k * mu c w) =
      fun s w => k * partCount (yzBoundary i) (modeGroup (yzMode i)) mu s w := by
    funext s w
    exact part_count_scale _ _ _ _ _ _
  rw [heq, potential_scale]

/-- Uniform replication scales the minimum of the three summed regional
rates exactly; normalized parent profiles and entropy penalties are unchanged. -/
private theorem mme_regional_rate_scale {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → W → ℕ) (k : ℕ) (hk : 0 < k) :
    regionalRate htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun i c w => k * mu i c w) = (k : ℝ) * regionalRate htotal n m mu := by
  simp only [regionalRate, coarse_potential_scale, penalty_potential_scale n m k hk,
    parent_potential_scale htotal n m _ k hk, compatibility_potential_scale,
    ← mul_sub, mul_min_of_nonneg _ _ (Nat.cast_nonneg k)]

/-- The entropy exponent controlling the hash scale is linear under uniform
replication, with the tolerance fixed before choosing the replication factor. -/
private theorem mme_regional_scale_exponent_scale {half R ell : ℕ}
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (eps : ℝ) (k : ℕ) (hk : 0 < k) :
    scaleExponent htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun i c w => k * mu i c w) eps =
        (k : ℝ) * scaleExponent htotal n m mu eps := by
  rw [scaleExponent, scaleExponent, mme_regional_joint_potential_scale,
    mme_regional_rate_scale htotal n m mu k hk]
  simp only [← Finset.mul_sum, Nat.cast_mul]
  ring


open BigOperators MME MME.RegionRate MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

private theorem replicated_size_le {R : ℕ} (n : Fin R → ℕ) (k : ℕ) :
    (((∑ r, k * n r : ℕ) : ℝ) + 1) ≤
      ((k : ℝ) + 1) * (((∑ r, n r : ℕ) : ℝ) + 1) := by
  rw [← Finset.mul_sum, Nat.cast_mul]
  nlinarith [(Nat.cast_nonneg (∑ r, n r) : (0 : ℝ) ≤ _), (Nat.cast_nonneg k : (0 : ℝ) ≤ _)]

private theorem polynomial_factor_scale_le {R : ℕ}
    (n : Fin R → ℕ) (k degree : ℕ) :
    polynomialFactor (fun r => k * n r) degree ≤
      ((k : ℝ) + 1) ^ degree * polynomialFactor n degree := by
  unfold polynomialFactor
  calc
    _ ≤ (((k : ℝ) + 1) * (6 * (((∑ r, n r : ℕ) : ℝ) + 1))) ^ degree := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [replicated_size_le n k]
    _ = _ := mul_pow _ _ _

private theorem ambient_factor_scale_le {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (k : ℕ) :
    ambientFactor (half := half) (parent := parent) (fun r => k * n r) ≤
      ((k : ℝ) + 1) ^ Fintype.card (Cell half R parent) *
        ambientFactor (half := half) (parent := parent) n := by
  unfold ambientFactor
  calc
    _ ≤ (((k : ℝ) + 1) * (((∑ r, n r : ℕ) : ℝ) + 1)) ^
        Fintype.card (Cell half R parent) := by
      gcongr
      exact replicated_size_le n k
    _ = _ := mul_pow _ _ _

/-- With the repair scale and profile types fixed, the prefactor in the
hash-scale estimate grows polynomially under replication of the parent sizes. -/
private theorem mme_regional_scale_factor_polynomial_replication
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
        apply mul_le_mul (ambient_factor_scale_le n k) (polynomial_factor_scale_le n k a)
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
        apply mul_le_mul (polynomial_factor_scale_le n k a) (polynomial_factor_scale_le n k b)
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

private theorem scale_factor_one_le {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) :
    1 ≤ scaleFactor (half := half) (parent := parent) n d ell := by
  have hload : 0 ≤ loadFactor (half := half) (parent := parent) n d ell := by
    unfold loadFactor ambientFactor polynomialFactor
    positivity
  unfold scaleFactor
  linarith [Nat.cast_nonneg (α := ℝ) half]

/-- The explicit polynomial prefactor contributes zero logarithmic cost per
replicated block in the limit, for any fixed repair scale and profile types. -/
private theorem mme_regional_scale_factor_log_div_tendsto_zero
    {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) :
    Tendsto (fun k : ℕ =>
      Real.log (scaleFactor (half := half) (parent := parent)
        (fun r => k * n r) d ell) / (k : ℝ)) atTop (nhds 0) := by
  let degree := max (Fintype.card (Cell half R parent) + R * (half + 1))
    (R * (half + 1) + R * (half + 1) *
      Fintype.card (Fin 2 → CompleteSplit.CompleteWord ell))
  let C := scaleFactor (half := half) (parent := parent) n d ell
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (scale_factor_one_le n d ell)
  have hlog (k : ℕ) :
      Real.log (scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell) ≤
        (degree : ℝ) * Real.log ((k : ℝ) + 1) + Real.log C := by
    have hpos : 0 < scaleFactor (half := half) (parent := parent) (fun r => k * n r) d ell :=
      lt_of_lt_of_le zero_lt_one (scale_factor_one_le _ d ell)
    have h := Real.log_le_log hpos (mme_regional_scale_factor_polynomial_replication n d ell k)
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
    (Real.log_nonneg (scale_factor_one_le _ d ell)) (Nat.cast_nonneg k))
    (fun k => div_le_div_of_nonneg_right (hlog k) (Nat.cast_nonneg k)) hupper


private theorem polynomial_factor_log_div_tendsto_zero {R : ℕ}
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
    have h := Real.log_le_log (hpos _) (polynomial_factor_scale_le n k degree)
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

private theorem sqrt_div_tendsto_zero_of_linear_rate (x : ℕ → ℝ) (rate : ℝ)
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
private theorem mme_regional_entropy_expression_log_rate
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
  have hfac := mme_regional_scale_factor_log_div_tendsto_zero (half := half) (parent := parent) n d ell
  have hpoly := polynomial_factor_log_div_tendsto_zero n (Fintype.card (Cell half R parent))
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
  have hsqrt := sqrt_div_tendsto_zero_of_linear_rate _ theta htheta
  have hmain := (((tendsto_const_nhds (x := rate - loss)).sub (hsqrt.const_mul 4)).sub
    (hi.const_mul (Real.log 32))).sub hpoly |>.sub hfac
  convert hmain.congr' ?_ using 1
  · simp [rate, loss]
  · filter_upwards [eventually_gt_atTop 0] with k hk
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hfactor : 0 < factor k :=
      lt_of_lt_of_le zero_lt_one (scale_factor_one_le _ d ell)
    have hpol : 0 < poly k := by dsimp [poly, polynomialFactor]; positivity
    rw [Real.log_div (Real.exp_ne_zero _) (mul_ne_zero
      (mul_ne_zero (by norm_num) hpol.ne') hfactor.ne'), Real.log_exp,
      Real.log_mul (mul_ne_zero (by norm_num) hpol.ne') hfactor.ne',
      Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hpol.ne']
    rw [mme_regional_rate_scale htotal n m mu k hk,
      mme_regional_scale_exponent_scale htotal n m mu eps k hk]
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

private theorem mme_regional_physical_common_scale_entropy_bound {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
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

private theorem mme_regional_physical_entropy_selected_bound {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
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
  have hs := mme_regional_physical_common_scale_entropy_bound htotal n m mu d eps heps ref href
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
private theorem mme_parent_histogram_sum_over_regions
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
private theorem mme_regional_parent_windows_imply_global_histogram_window
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
  have hcount := mme_parent_histogram_sum_over_regions positions f pair a
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
private theorem mme_cell_frequency_scale
    {C W : Type*} [Fintype W] (mu : C → W → ℕ)
    (k : ℕ) (hk : 0 < k) (c : C) (w : W) :
    cellFrequency (fun c w => k * mu c w) c w = cellFrequency mu c w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [cellFrequency, ← Finset.mul_sum, Nat.cast_mul]
  exact mul_div_mul_left _ _ hk'

/-- Uniform replication preserves the regional parent-mixture centers. -/
private theorem mme_parent_mixture_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (k : ℕ) (hk : 0 < k) (r : Fin R) (w : Fin 2 → W) :
    parentMixture htotal (fun r => k * n r) (fun r c => k * m r c)
      (fun c v => k * mu c v) r w = parentMixture htotal n m mu r w := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [parentMixture, mme_cell_frequency_scale mu k hk, Nat.cast_mul,
    mul_assoc, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hk'


open MME.Released116 MME.MoreAsymmetryExactSeed MME.CompleteSplit

/-- At every positive integer scale, the six regional windows imply a
full-word histogram window centered at the same released distribution. -/
private theorem mme_released_116_scaled_partition_parent_window (k : ℕ) (hk : 0 < k) :
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
  have h := mme_regional_parent_windows_imply_global_histogram_window
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
  simp only [mme_parent_mixture_scale _ _ _ _ k hk, hweight, hpair] at h
  rw [mme_released_116_weighted_parent_center i w] at h
  simp only [Fintype.card_eq_nat_card] at h ⊢
  exact h


/-- A partition of parent words induces a child-position order that agrees
with literal left/right splitting of the same fine word. -/
private theorem mme_regional_parent_partition_fine_coordinates
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
private theorem mme_released_116_scaled_fine_word_window (k : ℕ) (hk : 0 < k) :
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
  obtain ⟨positions, hwindow⟩ := mme_released_116_scaled_partition_parent_window k hk
  obtain ⟨childPositions, hsplit⟩ := mme_regional_parent_partition_fine_coordinates positions
  refine ⟨childPositions, ?_⟩
  intro i x eps htypical w
  have hfun := funext (hsplit x)
  rw [hfun] at htypical
  exact hwindow i (ProfiledCW.split (Equiv.refl _) rfl x) eps htypical w

private theorem mme_child_grading_implies_parent_grading
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (i : Fin 3) (a : Address half R parent n) (f : Position n → CompleteWord ell)
    (hf : Graded htotal i a f) (r : Fin R) (t : Fin (n r)) :
    (∑ h : Fin 2, ∑ q, (f ⟨r,t,h⟩ q).val) = parent r i := by
  rw [Fin.sum_univ_two, hf, hf]
  simp only [fullCell, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false]
  change ((a r t).val i).val + (parent r i - ((a r t).val i).val) = parent r i
  exact Nat.add_sub_of_le ((a r t).property.2 i)


private theorem grade_split_three (w : CompleteWord 3) :
    (∑ q, (w q).val) = ∑ h : Fin 2, ∑ q,
      ((![(completeWordSplitEquiv 2 (by decide) w).1,
        (completeWordSplitEquiv 2 (by decide) w).2] h) q).val := by
  simp [Fin.sum_univ_succ, completeWordSplitEquiv, fineWordSplitEquiv]
  omega

/-- The released histogram window and exact parent grades hold for the same
physical fine word whenever its child words are graded and parent typical. -/
private theorem mme_released_116_scaled_graded_fine_word_window (k : ℕ) (hk : 0 < k) :
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
  obtain ⟨positions, hwindow⟩ := mme_released_116_scaled_partition_parent_window k hk
  obtain ⟨childPositions, hsplit⟩ := mme_regional_parent_partition_fine_coordinates positions
  refine ⟨childPositions, ?_⟩
  intro i a x eps hg ht
  constructor
  · intro p
    obtain ⟨⟨r,t⟩, rfl⟩ := positions.surjective p
    have h := mme_child_grading_implies_parent_grading parent_total i a _ hg r t
    simp only [hsplit] at h
    rw [grade_split_three]
    exact h
  · have hfun := funext (hsplit x)
    rw [hfun] at ht
    exact hwindow i (ProfiledCW.split (Equiv.refl _) rfl x) eps ht



open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false

private theorem mme_exact_step_source_refinement_on_unbroken
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

private theorem split_flatten {S : Type} {ell L M : ℕ} (positions : Fin L ≃ S)
    (length : L * 2 ^ (ell - 1) = M) (f : S → CompleteSplit.CompleteWord ell) :
    ProfiledCW.split positions length (ProfiledCW.flatten positions length f) = f := by
  funext p h
  simp [ProfiledCW.split, ProfiledCW.flatten]

private theorem mme_recursive_region_graded_source_exact_step_realization {half R ell N L M : ℕ}
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
    simp only [P, split_flatten]
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
    mme_exact_step_source_refinement_on_unbroken E hincl
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [hcount] using hIc
  · exact hexponent
  · exact houtput


open MME.ProfiledCW MME.RecursiveYZ.CWCells

/-- The concrete released integer profiles give an exact extraction from the
simultaneously graded global histogram window at every admissible scale. -/
private theorem mme_released_116_graded_histogram_exact_step_with_repair_scale
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
  obtain ⟨positions, hwindow⟩ := mme_released_116_scaled_graded_fine_word_window k hk
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
  apply mme_recursive_region_graded_source_exact_step_realization parent
    (fun r => k * regionalSize r) parent_total (by decide)
    (fun r c => k * splitCount r c) e positions (by omega)
    (fun i c w => k * integerProfile i c w) hmass hsupport hboundary reference href
    (k * denominator ^ 2) d hminimum hd hsize hdiv eps heps hscale
  intro i a ha f hg ht
  have h := hwindow i a (ProfiledCW.flatten positions (by omega) f) eps
  rw [split_flatten] at h
  exact h hg ht

private theorem mme_released_116_arbitrarily_large_size_test
    (stride : ℕ) (hstride : 0 < stride)
    (d : ℕ) (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧ stride ∣ k ∧
      (8 * d : ℝ) * (25 * 6 *
        (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2) ≤
        (k * denominator ^ 2 : ℕ) * eps ^ 2 := by
  let B : ℝ := (8 * d : ℝ) * (25 * 6 *
    (Fintype.card (CompleteSplit.CompleteWord 2) : ℝ) ^ 2)
  have hfactor : 0 < (denominator : ℝ) ^ 2 * eps ^ 2 := by
    exact mul_pos (by norm_num [denominator]) (sq_pos_of_pos heps)
  obtain ⟨j, hj⟩ := exists_nat_gt (B / ((denominator : ℝ) ^ 2 * eps ^ 2))
  let k := 2 * (stride * max K (j + 1))
  have hlarge : max K (j + 1) ≤ k := by
    have hs : 1 ≤ stride := hstride
    have hm := Nat.mul_le_mul_right (max K (j + 1)) hs
    simp only [one_mul] at hm
    dsimp [k]
    omega
  have hK : K ≤ k := (le_max_left K (j + 1)).trans hlarge
  have hjk : j < k := (Nat.lt_succ_self j).trans_le
    ((le_max_right K (j + 1)).trans hlarge)
  have heven : Even k := ⟨stride * max K (j + 1), by dsimp [k]; omega⟩
  have hmultiple : stride ∣ k := ⟨2 * max K (j + 1), by dsimp [k]; ring⟩
  have hkr : (j : ℝ) < k := by exact_mod_cast hjk
  have hB : B < (k : ℝ) * ((denominator : ℝ) ^ 2 * eps ^ 2) :=
    (div_lt_iff₀ hfactor).mp (hj.trans hkr)
  refine ⟨k, hK, lt_of_le_of_lt (Nat.zero_le j) hjk, heven, hmultiple, ?_⟩
  simpa only [B, Nat.cast_mul, Nat.cast_pow, mul_assoc] using hB.le

/-- Every positive tolerance admits arbitrarily large replicated released
profiles with a quantitative exact extraction from the graded histogram window. -/
private theorem mme_released_116_cofinal_graded_histogram_exact_step_with_repair_scale
    (stride : ℕ) (hstride : 0 < stride)
    (d : ℕ) (hd : 1 < d) (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧ stride ∣ k ∧
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
  obtain ⟨k, hK, hk, heven, hmultiple, hscale⟩ := mme_released_116_arbitrarily_large_size_test stride hstride d eps heps K
  exact ⟨k, hK, hk, heven, hmultiple, mme_released_116_graded_histogram_exact_step_with_repair_scale d hd k hk eps heps hscale⟩


open MME MME.ProfiledCW
set_option autoImplicit false

/-- Repair divides the selected count by its power-of-eight budget;
the integer rounding loses strictly less than one additional copy. -/
private theorem mme_exact_step_copies_gt_normalized_count_sub_one
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

universe u

/-- The actual tensor restriction retains the post-repair copy count,
with its quantitative lower bound including the integer-rounding loss. -/
private theorem mme_exact_step_quantitative_tensor_restriction
    {K : Type u} [Field K] {ell N : ℕ} {P : Predicate N}
    (E : ExactStep ell N P) {B : ℝ} (hB : B ≤ E.count) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin E.copies => tensor K E.output)) (tensor K P) ∧
      B / (8 : ℝ) ^ E.stage.repairExponent - 1 < E.copies := by
  exact ⟨mme_recursive_profiled_CW_exact_step E,
    mme_exact_step_copies_gt_normalized_count_sub_one E hB⟩

/-- Cofinal released profiles give actual tensor restrictions over any field,
with all repair and integer-rounding losses retained in the copy bound. -/
private theorem mme_released_116_cofinal_graded_histogram_tensor_restriction
    (stride : ℕ) (hstride : 0 < stride)
    {KField : Type u} [Field KField] (d : ℕ) (hd : 1 < d) (eps : ℝ) (heps : 0 < eps) (K : ℕ) :
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧ stride ∣ k ∧
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
  obtain ⟨k, hK, hk, heven, hmultiple, positions, reference, href, E, hcount, hexponent, houtput⟩ :=
    mme_released_116_cofinal_graded_histogram_exact_step_with_repair_scale stride hstride d hd eps heps K
  exact ⟨k, hK, hk, heven, hmultiple, positions, reference, href, E, hcount, hexponent, houtput,
    mme_exact_step_quantitative_tensor_restriction E hcount⟩



set_option autoImplicit false

/-- The repair budget has logarithmic cost controlled by the capacity,
with the base-change factor exposed for choosing the repair scale. -/
private theorem mme_repair_budget_log_le (d C : ℕ) :
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
private theorem mme_repair_scale_exists_uniform_log_loss (delta : ℝ) (hdelta : 0 < delta) :
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
  refine ⟨d, hd, fun C => (mme_repair_budget_log_le d C).trans ?_⟩
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_right hratio (Real.log_natCast_nonneg C))


open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open scoped Classical
set_option autoImplicit false

/-- Every graded profile is a subset of the complete-word functions on its
positions, so three mode profiles have at most the unrestricted triple count. -/
private theorem mme_profile_capacity_le_unrestricted
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
private theorem mme_profile_capacity_log_le_fine_length
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
      exact_mod_cast mme_profile_capacity_le_unrestricted ell cell shape mu
    have h := Real.log_le_log hpos hbound
    rw [Real.log_pow] at h
    exact h


/-- One repair scale makes the logarithmic repair budget at most eta per
fine coordinate, up to the fixed log-eight overhead, for every profile. -/
private theorem mme_profile_repair_scale_exists_uniform_coordinate_loss
    (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℕ, 1 < d ∧ ∀ (ell : ℕ) (P C : Type*) [Fintype P]
      (cell : P → C) (shape : C → Fin 3 → ℕ)
      (mu : Fin 3 → C → CompleteWord ell → ℕ),
      Real.log ((8 : ℝ) ^ (Nat.log d
        (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) + 1)) ≤
        Real.log 8 + eta * (Fintype.card P * 2 ^ (ell - 1) : ℕ) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hden : 0 < 3 * Real.log 3 := mul_pos (by norm_num) h3
  obtain ⟨d, hd, hbudget⟩ := mme_repair_scale_exists_uniform_log_loss
    (eta / (3 * Real.log 3)) (div_pos heta hden)
  refine ⟨d, hd, ?_⟩
  intro ell P C inst cell shape mu
  have hcap := mme_profile_capacity_log_le_fine_length ell cell shape mu
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
private theorem mme_released_116_scaled_fine_coordinate_card (k : ℕ) :
    Fintype.card (Position (fun r : Fin 6 => k * regionalSize r)) * 2 ^ (2 - 1) =
      4 * (k * denominator ^ 4) := by
  simp only [Position, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
  rw [← Finset.sum_mul, ← Finset.mul_sum, mme_released_116_regional_total]
  ring

/-- One repair scale controls every replicated released profile, uniformly
in the reference address, at eta per physical fine coordinate. -/
private theorem mme_released_116_uniform_repair_coordinate_loss (eta : ℝ) (heta : 0 < eta) :
    ∃ d : ℕ, 1 < d ∧ ∀ (k : ℕ)
      (reference : MME.RecursiveXHash.Address 4 6 parent
        (fun r => k * regionalSize r)),
      Real.log ((8 : ℝ) ^ (Nat.log d
        (∏ i : Fin 3, Nat.card (Block 2 (fullCell parent_total reference)
          (fun c i => (c.2.val i).val) (fun i c w => k * integerProfile i c w) i)) + 1)) ≤
        Real.log 8 + eta * (4 * (k * denominator ^ 4) : ℕ) := by
  obtain ⟨d, hd, hbudget⟩ := mme_profile_repair_scale_exists_uniform_coordinate_loss eta heta
  refine ⟨d, hd, ?_⟩
  intro k reference
  have h := hbudget 2 _ _ (fullCell parent_total reference)
    (fun c i => (c.2.val i).val) (fun i c w => k * integerProfile i c w)
  rw [mme_released_116_scaled_fine_coordinate_card] at h
  exact h


/-- A single repair scale gives cofinal actual released tensor restrictions
with arbitrarily small repair loss per fine coordinate. The scale is fixed
before choosing the replication lower bound. -/
private theorem mme_released_116_cofinal_tensor_restriction_uniform_repair_loss
    (stride : ℕ) (hstride : 0 < stride)
    {KField : Type u} [Field KField] (eta : ℝ) (heta : 0 < eta) (eps : ℝ) (heps : 0 < eps) :
    ∃ d : ℕ, 1 < d ∧ ∀ K : ℕ,
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧ stride ∣ k ∧
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
  obtain ⟨d, hd, hbudget⟩ := mme_released_116_uniform_repair_coordinate_loss eta heta
  refine ⟨d, hd, ?_⟩
  intro K
  dsimp only
  obtain ⟨k, hK, hk, heven, hmultiple, positions, reference, href, E, hcount, hexponent,
    houtput, hrestrict, hcopies⟩ :=
    mme_released_116_cofinal_graded_histogram_tensor_restriction stride hstride
      (KField := KField) d hd eps heps K
  refine ⟨k, hK, hk, heven, hmultiple, positions, reference, href, E, hcount, hexponent, ?_,
    houtput, hrestrict, hcopies⟩
  rw [hexponent]
  exact hbudget k reference


end Extraction

namespace EventualBound
open Filter Topology
set_option autoImplicit false

/-- A strict gap between an asymptotic logarithmic rate and a linear repair
cost eventually pays any fixed overhead. -/
private theorem mme_eventually_log_exceeds_linear_cost (B : ℕ → ℝ) (rate cost overhead : ℝ)
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
universe u

private theorem survival_scale_factor_pos {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (n : Fin R → ℕ) (d ell : ℕ) :
    0 < scaleFactor (half := half) (parent := parent) n d ell := by
  unfold scaleFactor loadFactor ambientFactor polynomialFactor
  positivity

private theorem survival_polynomial_factor_pos {R : ℕ} (n : Fin R → ℕ) (degree : ℕ) :
    0 < polynomialFactor n degree := by
  unfold polynomialFactor
  positivity

/-- Repair divides the selected count by its power-of-eight budget;
the integer rounding loses strictly less than one additional copy. -/
private theorem mme_exact_step_copies_gt_normalized_count_sub_one
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


/-- Once the selected-count lower bound is at least twice the repair budget,
there are surviving copies and their log count loses only the explicit repair
cost and one log-two rounding allowance. -/
private theorem mme_exact_step_positive_copies_log_lower_bound
    {ell N : ℕ} {P : Predicate N} (E : ExactStep ell N P) {B : ℝ}
    (hB : B ≤ E.count) (hlarge : 2 * (8 : ℝ) ^ E.stage.repairExponent ≤ B) :
    0 < E.copies ∧ Real.log B -
      (E.stage.repairExponent : ℝ) * Real.log 8 - Real.log 2 < Real.log E.copies := by
  let D : ℝ := (8 : ℝ) ^ E.stage.repairExponent
  have hD : 0 < D := pow_pos (by norm_num) _
  have hBpos : 0 < B := lt_of_lt_of_le (mul_pos (by norm_num) hD) hlarge
  have htwo : 2 ≤ B / D := (le_div_iff₀ hD).mpr hlarge
  have hcopy := mme_exact_step_copies_gt_normalized_count_sub_one E hB
  have hlower : B / D / 2 < (E.copies : ℝ) := by
    change B / D - 1 < (E.copies : ℝ) at hcopy
    linarith
  have hpos : 0 < B / D / 2 := div_pos (div_pos hBpos hD) (by norm_num)
  have hcopies : 0 < (E.copies : ℝ) := hpos.trans hlower
  refine ⟨by exact_mod_cast hcopies, ?_⟩
  have hlog := Real.log_lt_log hpos hlower
  rw [Real.log_div (div_pos hBpos hD).ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_div hBpos.ne' hD.ne'] at hlog
  simpa only [D, Real.log_pow] using hlog


/-- At every sufficiently small positive tolerance, actual released tensor
restrictions exist cofinally at even multiples of any positive prescribed stride,
with log copy count greater than kN/20. -/
theorem solution
    (stride : ℕ) (hstride : 0 < stride)
    {KField : Type u} [Field KField]  :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
    ∃ d : ℕ, 1 < d ∧ ∀ K : ℕ,
    ∃ k : ℕ, K ≤ k ∧ 0 < k ∧ Even k ∧ stride ∣ k ∧
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
        ((∑ r, regionalSize r : ℕ) : ℝ) / 20 * (k : ℝ) < Real.log E.copies ∧
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
  obtain ⟨eps0, heps0, hrate⟩ := RateBound.mme_released_116_small_tolerance_rate_lower
  refine ⟨eps0, heps0, ?_⟩
  intro eps heps hepsle
  obtain ⟨d, hd, hcofinal⟩ :=
    Extraction.mme_released_116_cofinal_tensor_restriction_uniform_repair_loss stride hstride
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
  have hlim := AsymptoticBound.mme_regional_entropy_expression_log_rate
    parent_total regionalSize splitCount integerProfile eps d
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast (show 0 < ∑ r, regionalSize r by decide +kernel)
  have hgap : N / 10 < regionalRate parent_total regionalSize splitCount integerProfile -
      N * entropyModulus (Fin 2 → CompleteWord 2) eps := by
    have h := hrate eps heps.le hepsle
    change (3 / 20 : ℝ) * N ≤ _ at h
    linarith
  have hev := EventualBound.mme_eventually_log_exceeds_linear_cost B _ (N / 10)
    (Real.log 2 + Real.log 8) hlim hgap
  obtain ⟨K0, hK0⟩ := Filter.eventually_atTop.mp hev
  intro K
  obtain ⟨k, hK, hk, heven, hmultiple, positions, reference, href, E, hcount, hexponent,
    hrepair, houtput, hrestrict, hcopies⟩ := hcofinal (max K K0)
  have hsurvive : 0 < E.copies ∧ N / 20 * (k : ℝ) < Real.log E.copies := by
    have hselected := PhysicalBound.mme_regional_physical_entropy_selected_bound
      parent_total (size k) (counts k) (profiles k) d eps heps.le reference href
    have hf : 0 < factor k := by
      change 0 < scaleFactor (half := 4) (parent := parent) (size k) d 2
      exact survival_scale_factor_pos (size k) d 2
    have hp : 0 < polynomialFactor (size k) (Fintype.card (Cell 4 6 parent)) :=
      survival_polynomial_factor_pos _ _
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
    have hmargin : 0 ≤ N / 20 * (k : ℝ) :=
      mul_nonneg (div_nonneg hN.le (by norm_num)) (Nat.cast_nonneg _)
    have hlarge : 2 * (8 : ℝ) ^ E.stage.repairExponent < B k := by
      apply (Real.log_lt_log_iff (mul_pos (by norm_num) hD) hB).mp
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hD.ne']
      linarith
    have hcountB : B k ≤ (E.count : ℝ) := hselected.trans hcount
    obtain ⟨hpos, hcopyrate⟩ := mme_exact_step_positive_copies_log_lower_bound E hcountB hlarge.le
    refine ⟨hpos, ?_⟩
    rw [Real.log_pow] at hbudget
    linarith only [hcopyrate, hlog, hbudget]
  exact ⟨k, (le_max_left K K0).trans hK, hk, heven, hmultiple, positions, reference, href,
    E, hsurvive.1, hsurvive.2, hcount, hexponent, hrepair, houtput, hrestrict, hcopies⟩


#print axioms solution
