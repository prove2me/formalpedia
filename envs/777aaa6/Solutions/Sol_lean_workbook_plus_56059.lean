-- Prove2me | solution 1 for lean_workbook_plus_56059
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:19:26.382173+00:00
-- url     : https://prove2.me/submissions/46f00edc-8c5f-4f21-8ef1-a7f58fa61415

import Mathlib

namespace QuarticRadicalRatioSharpBound

noncomputable def radius (x : ℝ) : ℝ := Real.sqrt (x ^ 4 + 3)

theorem quartic_gap (x : ℝ) :
    x ^ 4 + 3 - (x + 1) ^ 2 = (x - 1) ^ 2 * ((x + 1) ^ 2 + 1) := by ring

theorem radius_positive (x : ℝ) : 0 < radius x := by
  unfold radius
  positivity

theorem radical_bound (x : ℝ) : |x + 1| ≤ radius x := by
  have hr : (radius x) ^ 2 = x ^ 4 + 3 := Real.sq_sqrt (by positivity)
  have hg : 0 ≤ x ^ 4 + 3 - (x + 1) ^ 2 := by
    rw [quartic_gap]
    positivity
  apply (sq_le_sq₀ (abs_nonneg (x + 1)) (radius_positive x).le).mp
  rw [sq_abs, hr]
  linarith

theorem radical_equality (x : ℝ) : radius x = |x + 1| ↔ x = 1 := by
  constructor
  · intro he
    have hr : (radius x) ^ 2 = x ^ 4 + 3 := Real.sq_sqrt (by positivity)
    rw [he, sq_abs] at hr
    have hg : (x - 1) ^ 2 * ((x + 1) ^ 2 + 1) = 0 := by
      rw [← quartic_gap]
      linarith only [hr]
    have hp : 0 < (x + 1) ^ 2 + 1 := by positivity
    have hs := (mul_eq_zero.mp hg).resolve_right (ne_of_gt hp)
    have hx := sq_eq_zero_iff.mp hs
    linarith
  · rintro rfl
    norm_num [radius]

theorem ratio_bound (x : ℝ) (hx : 0 ≤ x) : x / radius x ≤ x / (x + 1) := by
  have hd : 0 < x + 1 := by linarith
  have hr : x + 1 ≤ radius x := (le_abs_self (x + 1)).trans (radical_bound x)
  exact div_le_div_of_nonneg_left hx hd hr

theorem ratio_equality (x : ℝ) (hx : 0 ≤ x) :
    x / (x + 1) = x / radius x ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro he
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    · have hd : 0 < x + 1 := by linarith
      have hc := (div_eq_div_iff (ne_of_gt hd) (ne_of_gt (radius_positive x))).mp he
      have hr := mul_left_cancel₀ hx0 hc
      have hr' : radius x = |x + 1| := by
        rw [abs_of_nonneg hd.le]
        exact hr
      exact Or.inr ((radical_equality x).mp hr')
  · rintro (rfl | rfl)
    · simp only [zero_div]
    · have hr : radius 1 = 2 := by norm_num [radius]
      rw [hr]
      norm_num

theorem strict_ratio_iff (x : ℝ) (hx : 0 ≤ x) :
    x / radius x < x / (x + 1) ↔ x ≠ 0 ∧ x ≠ 1 := by
  constructor
  · intro h
    have hn : x / (x + 1) ≠ x / radius x := ne_of_gt h
    have hp : ¬ (x = 0 ∨ x = 1) := fun h => hn ((ratio_equality x hx).mpr h)
    exact not_or.mp hp
  · intro h
    apply lt_of_le_of_ne (ratio_bound x hx)
    intro he
    rcases (ratio_equality x hx).mp he.symm with h0 | h1
    · exact h.1 h0
    · exact h.2 h1

end QuarticRadicalRatioSharpBound

theorem solution (x : NNReal) : x / (x + 1) ≥ x / (Real.sqrt (x ^ 4 + 3)) := by
  simpa [QuarticRadicalRatioSharpBound.radius] using
    QuarticRadicalRatioSharpBound.ratio_bound (x : ℝ) x.property

#print axioms QuarticRadicalRatioSharpBound.quartic_gap
#print axioms QuarticRadicalRatioSharpBound.radius_positive
#print axioms QuarticRadicalRatioSharpBound.radical_bound
#print axioms QuarticRadicalRatioSharpBound.radical_equality
#print axioms QuarticRadicalRatioSharpBound.ratio_bound
#print axioms QuarticRadicalRatioSharpBound.ratio_equality
#print axioms QuarticRadicalRatioSharpBound.strict_ratio_iff
#print axioms solution
