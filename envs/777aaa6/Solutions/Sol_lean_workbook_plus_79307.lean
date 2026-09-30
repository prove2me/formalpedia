-- Prove2me | solution 1 for lean_workbook_plus_79307
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:35:21.672458+00:00
-- url     : https://prove2.me/submissions/c22705d5-aa8c-4ea4-823b-0b1ef79bb6aa

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ^ 3 * b ^ 2 + b ^ 3 * a ^ 2 + b ^ 3 * c ^ 2 + c ^ 3 * b ^ 2 +
      c ^ 3 * a ^ 2 + a ^ 3 * c ^ 2 ≥
      a * b * c * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) := by
  have hq : 0 ≤ (a * b + b * c + c * a) ^ 2 -
      3 * (a + b + c) * (a * b * c) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
      sq_nonneg (c * a - a * b)]
  have hp := mul_nonneg (add_nonneg (add_nonneg ha hb) hc) hq
  nlinarith only [hp]

#print axioms solution
