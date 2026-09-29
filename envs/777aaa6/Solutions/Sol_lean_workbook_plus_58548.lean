-- Prove2me | solution 1 for lean_workbook_plus_58548
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:55.419408+00:00
-- url     : https://prove2.me/submissions/22db70c7-35a5-4e6e-912b-0b650eb40926

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x * y) / (x + y) ≤ 1 / 4 * (x + y) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos hx hy])
