-- Prove2me | solution 1 for lean_workbook_plus_66090
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:39.854743+00:00
-- url     : https://prove2.me/submissions/b8e2c0ac-9f66-4c39-a4e4-0b0798cec08e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b k : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 + k) * a + b * (k - 2 + b / a) ≥ k * (a + b) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (k), sq_nonneg (a - b), sq_nonneg (a - k), sq_nonneg (b - k), sq_nonneg (a + b), sq_nonneg (a + k), sq_nonneg (b + k), mul_pos ha hb])
