-- Prove2me | solution 1 for lean_workbook_plus_35674
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:42:55.370876+00:00
-- url     : https://prove2.me/submissions/2885a94f-3c80-4f2d-9b3e-62b3e8a457a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (k : ℝ) (h₁ : x = y + k) (h₂ : k > 0) (h₃ : x^2 + y^2 = 1) : 2*y^2 + 2*y*k + k^2 = 1 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (k), sq_nonneg (x - y), sq_nonneg (x - k), sq_nonneg (y - k), sq_nonneg (x + y), sq_nonneg (x + k), sq_nonneg (y + k)])
