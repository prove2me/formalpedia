-- Prove2me | solution 1 for CongruentNumber.rational_triangle_iff_curve_point
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T07:24:41.768678+00:00
-- url     : https://prove2.me/submissions/c044b816-4982-41ab-92e1-7b59cd52edca

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

set_option autoImplicit false

/-- The algebraic triangle/elliptic-curve correspondence, with the mission's signed-side convention. -/
theorem solution (n : ℚ) (hn : 0 < n) :
    (∃ a b c : ℚ, a ^ 2 + b ^ 2 = c ^ 2 ∧ n = (2⁻¹ : ℚ) * a * b) ↔
      ∃ x y : ℚ, y ≠ 0 ∧ y ^ 2 = x ^ 3 - n ^ 2 * x := by
  constructor
  · rintro ⟨a,b,c,hpy,ha⟩
    have ha₀ : a ≠ 0 := by
      intro h
      simp [h] at ha
      linarith
    have hb₀ : b ≠ 0 := by
      intro h
      simp [h] at ha
      linarith
    have hac : a+c ≠ 0 := by
      intro h
      have hc : c = -a := by linarith
      rw [hc] at hpy
      have hb : b = 0 := by nlinarith
      exact hb₀ hb
    refine ⟨a*(a+c)/2,a^2*(a+c)/2,?_,?_⟩
    · exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 ha₀) hac) (by norm_num)
    · rw [ha]
      linear_combination (a^3*(a+c)/8)*hpy
  · rintro ⟨x,y,hy,hcurve⟩
    refine ⟨(x^2-n^2)/y,2*n*x/y,(x^2+n^2)/y,?_,?_⟩
    · field_simp
      ring
    · field_simp
      linear_combination hcurve
