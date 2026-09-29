-- Prove2me | solution 1 for lean_workbook_plus_47745
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:09.865481+00:00
-- url     : https://prove2.me/submissions/6f4d2e51-550a-4c0e-b737-f017e763970c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 5 * (a ^ 4 + b ^ 4 + c ^ 4) + a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 ≥ 2 * (a ^ 3 * (b + c) + b ^ 3 * (c + a) + c ^ 3 * (a + b) + a * b * c * (a + b + c)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
