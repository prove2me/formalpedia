-- Prove2me | solution 1 for lean_workbook_plus_19731
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:04:41.720749+00:00
-- url     : https://prove2.me/submissions/47f07dea-851d-4e00-8594-db9f7f27bfd9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z: ℝ) (h₁ : x + y + z = 0) (h₂ : x^3 + y^3 + z^3 = 0) : x*y*z = 0 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
