-- Prove2me | solution 1 for mme_released_116_regional_rate_lower
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T00:12:45.876415+00:00
-- url     : https://prove2.me/submissions/6937333d-586f-4a0b-9eb8-d0fa95e57920

import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_released_116_regional_split_mass
import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_released_116_integer_profile_support
import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

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
theorem solution :
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
  exact lt_of_lt_of_le (mul_pos (by norm_num) hn') solution


#print axioms solution
