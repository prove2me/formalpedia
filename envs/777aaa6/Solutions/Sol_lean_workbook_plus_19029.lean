-- Prove2me | solution 1 for lean_workbook_plus_19029
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:57:33.08396+00:00
-- url     : https://prove2.me/submissions/9cc52fb7-bee7-4644-a649-55c7e2d27514

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a^4 + a^4 + b^4 + c^4 ≥ 4 * a^2 * b * c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
