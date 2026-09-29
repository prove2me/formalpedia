-- Prove2me | solution 1 for lean_workbook_plus_54455
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:48:25.444951+00:00
-- url     : https://prove2.me/submissions/0bc9cb5b-f1a2-4a49-94f2-a0306578f7f9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) : (a^2 + b^2 + 1)^3 ≥ 3^3 * (a^2 * b^2) := by
  have hp := mul_nonneg (sq_nonneg (a^2+b^2-2)) (show 0 ≤ 4*(a^2+b^2)+1 by positivity)
  nlinarith [sq_nonneg (a^2-b^2)]
