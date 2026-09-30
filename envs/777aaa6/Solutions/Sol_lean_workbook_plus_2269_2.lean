-- Prove2me | solution 2 for lean_workbook_plus_2269
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:25:23.563215+00:00
-- url     : https://prove2.me/submissions/83efec13-84f9-495f-b831-e63958f95392

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v : ℝ) (hu : u > 0) (hv : v > 0) : (u + v) ^ 2 ≥ 4 * u * v := by
  (intros; nlinarith [sq_nonneg (u), sq_nonneg (v), sq_nonneg (u - v), sq_nonneg (u + v)])
