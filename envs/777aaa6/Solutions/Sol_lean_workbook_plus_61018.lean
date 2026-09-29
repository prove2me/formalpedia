-- Prove2me | solution 1 for lean_workbook_plus_61018
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:29.601832+00:00
-- url     : https://prove2.me/submissions/69f07985-bc49-485d-9b4e-f1a7291a74f7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^3 / (a^2 + a * b + b^2) : ℝ) ≥ (2 * a - b) / 3 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
