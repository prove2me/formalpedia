-- Prove2me | solution 1 for lean_workbook_plus_55127
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:19.454641+00:00
-- url     : https://prove2.me/submissions/52f9e4d6-adff-469f-abf7-6f0e18099ca2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : (1 - Real.sqrt 5) / 2 < 0 := by
  have h : (1 : ℝ) < Real.sqrt 5 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  linarith
