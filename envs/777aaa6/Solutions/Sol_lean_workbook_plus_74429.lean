-- Prove2me | solution 1 for lean_workbook_plus_74429
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T20:12:01.655519+00:00
-- url     : https://prove2.me/submissions/de826c97-8332-45b2-ad8f-6ea4f3e32c86

import Mathlib
set_option autoImplicit false

theorem solution  (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₁ : x ≠ y)
  (h₂ : y ≠ z)
  (h₃ : z ≠ x) :
  1 / Real.sqrt ((y / z) + (y / x) + 1 / 2) + 1 / Real.sqrt ((z / x) + (z / y) + 1 / 2) + 1 / Real.sqrt ((x / y) + (x / z) + 1 / 2) =
  Real.sqrt (2 * x * z / (2 * x * y + 2 * y * z + x * z)) + Real.sqrt (2 * y * x / (2 * y * z + 2 * z * x + y * x)) + Real.sqrt (2 * z * y / (2 * z * x + 2 * x * y + z * y))   := by
  have term (X Y Z : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) :
      1 / Real.sqrt (Y / Z + Y / X + 1 / 2) =
        Real.sqrt (2 * X * Z / (2 * X * Y + 2 * Y * Z + X * Z)) := by
    have hA : 0 < Y / Z + Y / X + (1 / 2 : ℝ) := by positivity
    have hD : 0 < 2 * X * Y + 2 * Y * Z + X * Z := by positivity
    have hfrac : 1 / (Y / Z + Y / X + (1 / 2 : ℝ)) =
        2 * X * Z / (2 * X * Y + 2 * Y * Z + X * Z) := by
      apply (div_eq_div_iff (ne_of_gt hA) (ne_of_gt hD)).2
      field_simp [ne_of_gt hX, ne_of_gt hZ] <;> ring
    calc
      1 / Real.sqrt (Y / Z + Y / X + 1 / 2) =
          Real.sqrt (1 / (Y / Z + Y / X + 1 / 2)) := by
        simp only [one_div, Real.sqrt_inv]
      _ = _ := congrArg Real.sqrt hfrac
  rw [term x y z h₀.1 h₀.2.1 h₀.2.2,
    term y z x h₀.2.1 h₀.2.2 h₀.1,
    term z x y h₀.2.2 h₀.1 h₀.2.1]

#print axioms solution
