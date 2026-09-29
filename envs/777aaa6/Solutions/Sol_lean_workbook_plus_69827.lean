-- Prove2me | solution 1 for lean_workbook_plus_69827
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:30:17.443841+00:00
-- url     : https://prove2.me/submissions/35711419-57c2-47a6-bc02-c3521529db09

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h : x^3 + y^3 + (x + y) / 4 = 15 / 2) : 0 < x + y ∧ x + y ≤ 3 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
