-- Prove2me | solution 1 for lean_workbook_plus_22356
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:44:53.585656+00:00
-- url     : https://prove2.me/submissions/786a9450-6bc4-4b84-866c-a9ea30205e10

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^3 / (a^2 + a * b + b^2) >= (2 * a - b) / 3) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
