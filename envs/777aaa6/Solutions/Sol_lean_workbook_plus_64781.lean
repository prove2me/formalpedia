-- Prove2me | solution 1 for lean_workbook_plus_64781
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:06:33.125811+00:00
-- url     : https://prove2.me/submissions/58ef1892-be7b-41e5-84c5-4ea5de647d57

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (e : ℝ)
  (h₀ : e = (2 + (3 + e) + (5 + e)) / 3) :
  e = 10 := by
  linarith
