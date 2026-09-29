-- Prove2me | solution 1 for lean_workbook_plus_14178
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:25.144737+00:00
-- url     : https://prove2.me/submissions/96ec17ca-9a84-42ea-9952-2630ae98f4cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c: ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ (a + b + c) ^ 2 ∧ (a + b + c) ^ 2 ≥ 3 * (a * b + b * c + c * a) := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
