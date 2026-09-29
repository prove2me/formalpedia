-- Prove2me | solution 1 for lean_workbook_plus_16048
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:34.179383+00:00
-- url     : https://prove2.me/submissions/58ab177c-9ef8-433d-9030-eed274eef621

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (1 / (a * b) + 1 / (a ^ 2 + a * b + b ^ 2)) ≥ (16 / 3) * (1 / (a ^ 2 + 2 * a * b + b ^ 2)) := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
