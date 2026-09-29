-- Prove2me | solution 1 for lean_workbook_plus_68518
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:50:31.730579+00:00
-- url     : https://prove2.me/submissions/aa5a0075-298a-4ee9-8d33-11a90ca971ab

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a > -1 ∧ b > -1)(h : a^3 + b^3 >= a^2 + b^2) : a^5 + b^5 >= a^2 + b^2   := by
  have ha : 0 ≤ a ^ 2 * (a - 1) ^ 2 * (a + 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg a) (sq_nonneg (a - 1))) (by linarith [hab.1])
  have hb : 0 ≤ b ^ 2 * (b - 1) ^ 2 * (b + 2) :=
    mul_nonneg (mul_nonneg (sq_nonneg b) (sq_nonneg (b - 1))) (by linarith [hab.2])
  nlinarith only [ha, hb, h]
