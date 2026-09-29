-- Prove2me | solution 1 for lean_workbook_plus_55671
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:21:42.53184+00:00
-- url     : https://prove2.me/submissions/daf9642c-8ea9-425f-bada-50df020f0268

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x ≥ y) (h₂ : y ≥ z) : (x - y) ^ 2 * (y - z) ^ 2 + 6 * (x - y) * (y - z) ≥ 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
