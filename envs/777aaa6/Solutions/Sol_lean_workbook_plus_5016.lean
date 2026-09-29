-- Prove2me | solution 1 for lean_workbook_plus_5016
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:16:21.559936+00:00
-- url     : https://prove2.me/submissions/39d7f77d-69c1-49db-893e-24227095453e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : 8 * x^3 + 1 = 3 * y)
  (h₁ : y^3 = 6 * x - 1) :
  8 * x^3 - y^3 = 3 * y - 6 * x → y = 2 * x := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
