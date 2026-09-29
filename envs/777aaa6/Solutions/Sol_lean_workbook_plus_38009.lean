-- Prove2me | solution 1 for lean_workbook_plus_38009
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:23.583574+00:00
-- url     : https://prove2.me/submissions/c6245624-925f-4d6e-b957-c036182d6373

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c d : ℝ) : Real.sqrt ((a^2 + d^2) * (b^2 + c^2)) ≥ a * c + b * d := by
  apply Real.le_sqrt_of_sq_le
  nlinarith only [sq_nonneg (a*b-c*d)]
