-- Prove2me | solution 1 for lean_workbook_plus_19961
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:37:14.962904+00:00
-- url     : https://prove2.me/submissions/33855871-01dc-4d58-af35-30c704cd4aac

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace ReciprocalDifferenceSharpConstant

def reciprocalSum (a b : ℝ) : ℝ := 1 / a ^ 2 + 1 / b ^ 2 + 1 / (a - b) ^ 2

def weight (a b : ℝ) : ℝ := 3 + 2 * a + 2 * b + a * b

def value (a b : ℝ) : ℝ := weight a b * reciprocalSum a b

def attainable : Set ℝ := {v | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ value a b = v}

theorem sum_positive (a b : ℝ) (ha : 0 < a) : 0 < reciprocalSum a b := by
  dsimp [reciprocalSum]
  positivity

theorem homogeneous_gap (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    a * b * reciprocalSum a b - 4 =
      (a ^ 2 - 3 * a * b + b ^ 2) ^ 2 / (a * b * (a - b) ^ 2) := by
  dsimp [reciprocalSum]
  field_simp [ha, hb, sub_ne_zero.mpr hab]
  ring

theorem homogeneous_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    4 ≤ a * b * reciprocalSum a b := by
  have h := homogeneous_gap a b ha.ne' hb.ne' hab
  have hp : 0 ≤ (a ^ 2 - 3 * a * b + b ^ 2) ^ 2 / (a * b * (a - b) ^ 2) := by
    positivity
  linarith only [h, hp]

theorem homogeneous_equality (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    a * b * reciprocalSum a b = 4 ↔ a ^ 2 - 3 * a * b + b ^ 2 = 0 := by
  have hd : a * b * (a - b) ^ 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero ha.ne' hb.ne') (pow_ne_zero _ (sub_ne_zero.mpr hab))
  rw [← sub_eq_zero, homogeneous_gap a b ha.ne' hb.ne' hab,
    div_eq_zero_iff, or_iff_left hd, pow_eq_zero_iff (by norm_num : 2 ≠ 0)]

theorem weight_positive (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < weight a b := by
  dsimp [weight]
  positivity

theorem strict_bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    4 < value a b := by
  have h := homogeneous_bound a b ha hb hab
  have hp := mul_pos (show 0 < 3 + 2 * a + 2 * b by positivity) (sum_positive a b ha)
  dsimp [value, weight]
  nlinarith only [h, hp]

theorem optimal_ratio :
    let r : ℝ := (3 + Real.sqrt 5) / 2
    1 < r ∧ r ^ 2 - 3 * r + 1 = 0 := by
  dsimp
  have hn := Real.sqrt_nonneg (5 : ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  constructor <;> nlinarith

theorem ray_value (r t : ℝ) (hr : 1 < r) (ht : 0 < t)
    (hq : r ^ 2 - 3 * r + 1 = 0) :
    value (r / t) (1 / t) = 4 + (8 * (r + 1) / r) * t + (12 / r) * t ^ 2 := by
  have hr0 : 0 < r := by linarith
  have ha : 0 < r / t := div_pos hr0 ht
  have hb : 0 < (1 : ℝ) / t := div_pos (by norm_num) ht
  have hab : r / t ≠ 1 / t := by
    exact ne_of_gt ((div_lt_div_iff_of_pos_right ht).mpr hr)
  have he : (r / t) ^ 2 - 3 * (r / t) * (1 / t) + (1 / t) ^ 2 = 0 := by
    field_simp
    nlinarith only [hq]
  have heq := (homogeneous_equality (r / t) (1 / t) ha hb hab).mpr he
  have hs : reciprocalSum (r / t) (1 / t) = 4 * t ^ 2 / r := by
    apply (eq_div_iff hr0.ne').mpr
    field_simp at heq
    nlinarith only [heq]
  dsimp [value, weight]
  rw [hs]
  field_simp
  ring

theorem arbitrarily_close (k : ℝ) (hk : 4 < k) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ value a b < k := by
  let r : ℝ := (3 + Real.sqrt 5) / 2
  obtain ⟨hr, hq⟩ := optimal_ratio
  change 1 < r at hr
  change r ^ 2 - 3 * r + 1 = 0 at hq
  have hr0 : 0 < r := by linarith
  let M : ℝ := 8 * (r + 1) / r + 12 / r
  have hM : 0 < M := by dsimp [M]; positivity
  have hmin : 0 < min (1 : ℝ) ((k - 4) / M) :=
    lt_min (by norm_num) (div_pos (sub_pos.mpr hk) hM)
  obtain ⟨t, ht, hsmall⟩ := exists_between hmin
  have ht1 : t < 1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have htM : t * M < k - 4 :=
    (lt_div_iff₀ hM).mp (lt_of_lt_of_le hsmall (min_le_right _ _))
  refine ⟨r / t, 1 / t, div_pos hr0 ht, div_pos (by norm_num) ht, ?_, ?_⟩
  · exact ne_of_gt ((div_lt_div_iff_of_pos_right ht).mpr hr)
  · rw [ray_value r t hr ht hq]
    have ht2 : t ^ 2 ≤ t := by nlinarith
    have h12 : 0 < 12 / r := by positivity
    dsimp [M] at htM
    nlinarith only [htM, mul_nonneg (le_of_lt h12) (sub_nonneg.mpr ht2)]

theorem uniform_value_lower_bound (k : ℝ) :
    (∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → k ≤ value a b) ↔ k ≤ 4 := by
  constructor
  · intro h
    by_contra hk
    obtain ⟨a, b, ha, hb, hab, hlt⟩ := arbitrarily_close k (lt_of_not_ge hk)
    exact (not_lt_of_ge (h a b ha hb hab)) hlt
  · intro hk a b ha hb hab
    exact hk.trans (strict_bound a b ha hb hab).le

theorem greatest_lower_bound : IsGLB attainable 4 := by
  constructor
  · rintro v ⟨a, b, ha, hb, hab, rfl⟩
    exact (strict_bound a b ha hb hab).le
  · intro k hk
    apply (uniform_value_lower_bound k).mp
    intro a b ha hb hab
    exact hk ⟨a, b, ha, hb, hab, rfl⟩

theorem not_attained : (4 : ℝ) ∉ attainable := by
  rintro ⟨a, b, ha, hb, hab, he⟩
  exact (ne_of_gt (strict_bound a b ha hb hab)) he

theorem no_least_value (v : ℝ) : ¬ IsLeast attainable v := by
  rintro ⟨⟨a, b, ha, hb, hab, he⟩, hmin⟩
  obtain ⟨c, d, hc, hd, hcd, hlt⟩ := arbitrarily_close v (he ▸ strict_bound a b ha hb hab)
  exact (not_lt_of_ge (hmin ⟨c, d, hc, hd, hcd, rfl⟩)) hlt

theorem uniform_source_constant (k : ℝ) :
    (∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → reciprocalSum a b ≥ k / weight a b) ↔
      k ≤ 4 := by
  have h : (∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → reciprocalSum a b ≥ k / weight a b) ↔
      (∀ a b : ℝ, 0 < a → 0 < b → a ≠ b → k ≤ value a b) := by
    constructor <;> intro h a b ha hb hab
    · simpa only [value, mul_comm] using (div_le_iff₀ (weight_positive a b ha hb)).mp (h a b ha hb hab)
    · apply (div_le_iff₀ (weight_positive a b ha hb)).mpr
      simpa only [value, mul_comm] using h a b ha hb hab
  exact h.trans (uniform_value_lower_bound k)

theorem source_expression (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (a ^ 2 * b ^ 2 + a ^ 2 * (a - b) ^ 2 + b ^ 2 * (a - b) ^ 2) /
      (a ^ 2 * b ^ 2 * (a - b) ^ 2) = reciprocalSum a b := by
  dsimp [reciprocalSum]
  field_simp [ha, hb, sub_ne_zero.mpr hab]
  ring

end ReciprocalDifferenceSharpConstant

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (a^2 * b^2 + a^2 * (a - b)^2 + b^2 * (a - b)^2) / (a^2 * b^2 * (a - b)^2) ≥
      4 / (3 + 2 * a + 2 * b + a * b) := by
  rw [ReciprocalDifferenceSharpConstant.source_expression a b ha.ne' hb.ne' hab]
  exact (ReciprocalDifferenceSharpConstant.uniform_source_constant 4).mpr le_rfl a b ha hb hab

#print axioms ReciprocalDifferenceSharpConstant.sum_positive
#print axioms ReciprocalDifferenceSharpConstant.homogeneous_gap
#print axioms ReciprocalDifferenceSharpConstant.homogeneous_bound
#print axioms ReciprocalDifferenceSharpConstant.homogeneous_equality
#print axioms ReciprocalDifferenceSharpConstant.weight_positive
#print axioms ReciprocalDifferenceSharpConstant.strict_bound
#print axioms ReciprocalDifferenceSharpConstant.optimal_ratio
#print axioms ReciprocalDifferenceSharpConstant.ray_value
#print axioms ReciprocalDifferenceSharpConstant.arbitrarily_close
#print axioms ReciprocalDifferenceSharpConstant.uniform_value_lower_bound
#print axioms ReciprocalDifferenceSharpConstant.greatest_lower_bound
#print axioms ReciprocalDifferenceSharpConstant.not_attained
#print axioms ReciprocalDifferenceSharpConstant.no_least_value
#print axioms ReciprocalDifferenceSharpConstant.uniform_source_constant
#print axioms ReciprocalDifferenceSharpConstant.source_expression
#print axioms solution
