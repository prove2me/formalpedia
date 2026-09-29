-- Prove2me | solution 1 for lean_workbook_plus_9793
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:50:39.802551+00:00
-- url     : https://prove2.me/submissions/8502ab5a-839a-4be2-9380-748ae15378b4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) : Real.sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) ≥ a * c + b * d := by
  apply Real.le_sqrt_of_sq_le
  nlinarith only [sq_nonneg (a*d-b*c)]
