-- Prove2me | solution 1 for lean_workbook_plus_8773
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:45.877925+00:00
-- url     : https://prove2.me/submissions/354134b1-1890-41e9-868b-2cdc7569ceb6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u v : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) : u^3 - u * v^2 + v^3 ≥ 0 := by
  (intros; nlinarith [sq_nonneg (u), sq_nonneg (v), sq_nonneg (u - v), sq_nonneg (u + v)])
