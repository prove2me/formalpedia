-- Prove2me | solution 1 for lean_workbook_plus_66381
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:32:13.228604+00:00
-- url     : https://prove2.me/submissions/fc16a623-0678-4f2e-9024-76cbc459d3b5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x + y = 3) (h₂ : x^2 + y^2 - x*y = 4) : x^4 + y^4 + x^3*y + x*y^3 = 36 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
