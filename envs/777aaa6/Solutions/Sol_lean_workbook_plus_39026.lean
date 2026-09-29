-- Prove2me | solution 1 for lean_workbook_plus_39026
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:30.235308+00:00
-- url     : https://prove2.me/submissions/f68ebd15-ec12-4b84-86a0-7a549e688c32

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 1 / (3 * a + b) + 1 / (a + 3 * b) ≤ (1 / 4) * (1 / a + 1 / b) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
