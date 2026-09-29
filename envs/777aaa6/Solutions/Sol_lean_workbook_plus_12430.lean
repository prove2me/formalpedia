-- Prove2me | solution 1 for lean_workbook_plus_12430
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:12:35.804569+00:00
-- url     : https://prove2.me/submissions/8d7f725b-5cba-44e6-b226-89ee76d11e85

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x y : ℝ) (hx : x > 0 ∧ y > 0 ∧ x * y = 9) (h : 1/x = 4 * 1/y) : x + y = 15/2 := by
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  have hy0 : y ≠ 0 := ne_of_gt hx.2.1
  have he : y = 4*x := by
    field_simp [hx0, hy0] at h
    nlinarith
  have hv : x = 3/2 := by nlinarith [hx.2.2, hx.1]
  linarith
