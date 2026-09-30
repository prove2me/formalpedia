-- Prove2me | solution 1 for lean_workbook_plus_79523
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:51.443143+00:00
-- url     : https://prove2.me/submissions/1181ff2d-2f45-43b3-b830-4961eb11ff55

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : (a + 1 / b) * (b + 1 / a) = 5) : a + b ≥ Real.sqrt 5 - 1 := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hpoly : (a * b) ^ 2 - 3 * (a * b) + 1 = 0 := by
    field_simp at hab
    nlinarith
  have hq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hq0 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have hlo : 0 ≤ Real.sqrt 5 - 1 := by nlinarith
  have hfactor : (2 * a * b - 3 + Real.sqrt 5) *
      (2 * a * b - 3 - Real.sqrt 5) = 0 := by nlinarith
  apply (sq_le_sq₀ hlo (le_of_lt (add_pos ha hb))).1
  rcases mul_eq_zero.mp hfactor with hroot | hroot
  all_goals nlinarith [sq_nonneg (a - b)]
