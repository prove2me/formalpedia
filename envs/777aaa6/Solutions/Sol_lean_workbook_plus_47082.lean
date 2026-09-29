-- Prove2me | solution 1 for lean_workbook_plus_47082
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:38:02.336392+00:00
-- url     : https://prove2.me/submissions/ec3d62c8-f32d-4f2e-93d4-a6705387941b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x = (5:ℝ)^(1/3)) (hy : y = (4:ℝ)^(1/3)) : 1/9 * (9 * x - 9 * y) = x - y := by
  (intros; simp_all)
