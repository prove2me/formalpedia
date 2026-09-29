-- Prove2me | solution 1 for lean_workbook_plus_47645
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:52:00.236609+00:00
-- url     : https://prove2.me/submissions/ca0eaccb-2d63-4120-a7a6-e02ff139ceac

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) (hx : x > 0) : x^3 + x + 1/x - x^2 > 3/2 := by
  have hi : x * (1/x)=1 := by field_simp
  have hp := mul_nonneg (sq_nonneg x) (sq_nonneg (x-1/2))
  have hq := sq_nonneg (x-1)
  by_contra hn
  have hm := mul_nonpos_of_nonneg_of_nonpos hx.le (show x^3+x+1/x-x^2-3/2 ≤ 0 by linarith)
  nlinarith
