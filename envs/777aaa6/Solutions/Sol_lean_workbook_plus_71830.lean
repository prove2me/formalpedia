-- Prove2me | solution 1 for lean_workbook_plus_71830
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:58:18.498808+00:00
-- url     : https://prove2.me/submissions/978d6581-6366-4eaf-a51d-485871438b1d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a * b ^ 3 + a * c ^ 3 + b * c ^ 3 + b * a ^ 3 + c * a ^ 3 + c * b ^ 3 ≤
      2 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  have h1 := mul_nonneg (sq_nonneg (a - b))
    (show 0 ≤ a ^ 2 + a * b + b ^ 2 by positivity)
  have h2 := mul_nonneg (sq_nonneg (b - c))
    (show 0 ≤ b ^ 2 + b * c + c ^ 2 by positivity)
  have h3 := mul_nonneg (sq_nonneg (c - a))
    (show 0 ≤ c ^ 2 + c * a + a ^ 2 by positivity)
  nlinarith only [h1, h2, h3]

#print axioms solution
