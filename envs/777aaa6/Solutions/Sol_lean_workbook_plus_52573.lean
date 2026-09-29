-- Prove2me | solution 1 for lean_workbook_plus_52573
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:20.371794+00:00
-- url     : https://prove2.me/submissions/864b337c-ae45-4d33-aa41-4adc41c3c1e7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) (h : abs x = abs y) : (x^2-y^2)^2 = 0 := by
  intros
  grind
