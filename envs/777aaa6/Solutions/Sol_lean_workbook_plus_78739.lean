-- Prove2me | solution 1 for lean_workbook_plus_78739
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:28:26.060776+00:00
-- url     : https://prove2.me/submissions/43fd8386-281b-4045-837c-a9aa20f29729

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 3 + b ^ 3 + c ^ 3 + a * b * c ≥
      a * (3 / 2 * b ^ 2 + 3 / 2 * c ^ 2 + b * c) := by
  have h₁ := mul_nonneg (sq_nonneg (a - b)) (show 0 ≤ a + 2 * b by positivity)
  have h₂ := mul_nonneg (sq_nonneg (a - c)) (show 0 ≤ a + 2 * c by positivity)
  nlinarith

#print axioms solution
