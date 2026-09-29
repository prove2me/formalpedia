-- Prove2me | solution 1 for lean_workbook_plus_19043
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:51:54.171719+00:00
-- url     : https://prove2.me/submissions/b57214ad-4a86-4197-bf02-459f5000bc04

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) : Real.sqrt ((a^2 + b^2) * (c^2 + d^2)) ≥ a * d + b * c := by
  apply Real.le_sqrt_of_sq_le
  nlinarith only [sq_nonneg (a*c-b*d)]
