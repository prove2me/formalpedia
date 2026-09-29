-- Prove2me | solution 1 for lean_workbook_plus_3526
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:56.312384+00:00
-- url     : https://prove2.me/submissions/53deb394-8852-475b-8b59-c5a7c1d937fb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : (6 : ℝ) ≤ (9 * Real.sqrt 2) / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith
