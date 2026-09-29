-- Prove2me | solution 1 for lean_workbook_plus_20066
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:19:25.340773+00:00
-- url     : https://prove2.me/submissions/9ccaa20a-49cf-4a53-84af-e050061c6c71

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ)
  (h₀ : abs b ≥ 2)
  (h₁ : a * c + 1 ≥ abs b) :
  (a * c + 1)^2 ≥ b^2 := by
  have hp := mul_nonneg (show 0 ≤ a*c+1-abs b by linarith) (show 0 ≤ a*c+1+abs b by linarith [abs_nonneg b])
  nlinarith [sq_abs b]
