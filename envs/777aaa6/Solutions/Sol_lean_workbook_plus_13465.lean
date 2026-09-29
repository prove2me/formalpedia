-- Prove2me | solution 1 for lean_workbook_plus_13465
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:45.277553+00:00
-- url     : https://prove2.me/submissions/ac6ce8c5-040e-4b72-ab8b-e917da35d051

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (k : ℝ) (h₁ : k ≥ 1) (h₂ : x^2 + y^2 + z^2 = k * (x * y + x * z + y * z)) : 3 * (k + 1)^3 ≥ 8 * (k + 2) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (k), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - k), sq_nonneg (y - z), sq_nonneg (y - k), sq_nonneg (z - k), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (x + k), sq_nonneg (y + z), sq_nonneg (y + k), sq_nonneg (z + k)])
