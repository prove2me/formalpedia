-- Prove2me | solution 1 for lean_workbook_plus_48431
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:26:46.911392+00:00
-- url     : https://prove2.me/submissions/2e8f9e36-f3ff-4d8b-bee2-a99c2188ee15

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d : ℝ) (h1 : a < b ∧ b < c ∧ c < d) : (a + b + c + d) ^ 2 ≥ 8 * (a * c + b * d) := by
  have hp := mul_nonneg (show 0 ≤ b-a by linarith [h1.1]) (show 0 ≤ c-b by linarith [h1.2.1])
  nlinarith [sq_nonneg (a-3*b+c+d)]
