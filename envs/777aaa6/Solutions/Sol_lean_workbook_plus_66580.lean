-- Prove2me | solution 1 for lean_workbook_plus_66580
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:03.340722+00:00
-- url     : https://prove2.me/submissions/d7456074-26a2-4c28-8cd3-5f8d50004f64

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ (a + b + c) * (2 * (a ^ 3 + b ^ 3 + c ^ 3) + 3 * a * b * c) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
