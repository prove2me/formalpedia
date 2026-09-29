-- Prove2me | solution 1 for lean_workbook_plus_48884
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:17.865473+00:00
-- url     : https://prove2.me/submissions/a7a5b629-1f6f-463a-8538-87e6bdefceb2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b : ℝ) (h : (a - Real.sqrt 7 * b) ^ 2 > 0) :
  a ^ 2 + 7 * b ^ 2 > 2 * Real.sqrt 7 * a * b := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by norm_num)
  have hm := congrArg (fun t : ℝ => t*b^2) hs
  nlinarith
