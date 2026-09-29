-- Prove2me | solution 1 for lean_workbook_plus_21953
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:40:26.212794+00:00
-- url     : https://prove2.me/submissions/2245f71c-1091-4407-9179-94679b541bad

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ)
  (h₀ : 0 < a)
  (h₁ : Real.sqrt (a * (a + 8)) = 15 / 2) :
  (a + (a + 8)) / 2 = 17 / 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ a*(a+8) by positivity)
  rw [h₁] at hs
  nlinarith
