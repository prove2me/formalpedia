-- Prove2me | solution 1 for lean_workbook_plus_19768
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:51.980963+00:00
-- url     : https://prove2.me/submissions/4d68eedf-703c-4f7f-85cb-4897cf5f3c77

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) :
  (a^4 + b^4 + c^4) + 3 * (b^2 * c^2 + c^2 * a^2 + a^2 * b^2) ≥
  2 * (b * c * (b^2 + c^2) + c * a * (c^2 + a^2) + a * b * (a^2 + b^2)) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
