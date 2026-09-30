-- Prove2me | solution 1 for lean_workbook_plus_78956
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:42:24.120097+00:00
-- url     : https://prove2.me/submissions/11606287-94c6-4e1c-b4f2-229284356c72

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * (a + 2 * b + c) = 2 * (b ^ 2 + 2 * c ^ 2)) :
    a / (2 * b + c) ≥ 1 / 3 := by
  have hprod : 0 ≤ (3 * a - (2 * b + c)) * (3 * a + 4 * (2 * b + c)) := by
    nlinarith [sq_nonneg (b - 4 * c)]
  have hlin : 0 ≤ 3 * a - (2 * b + c) :=
    nonneg_of_mul_nonneg_left hprod (by positivity)
  apply (le_div_iff₀ (by positivity : 0 < 2 * b + c)).mpr
  linarith

#print axioms solution
