-- Prove2me | solution 1 for lean_workbook_plus_75605
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:10:13.319464+00:00
-- url     : https://prove2.me/submissions/fef36a68-27e0-4d56-8b09-c7e85b05a93f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : x < 0) : x + 1/x ≤ -2 := by
  have hx0 : x≠0 := ne_of_lt hx
  have hi : x+1/x+2=(x+1)^2/x := by field_simp; ring
  have hp := div_nonpos_of_nonneg_of_nonpos (sq_nonneg (x+1)) hx.le
  linarith
