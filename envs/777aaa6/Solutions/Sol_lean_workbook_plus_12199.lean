-- Prove2me | solution 1 for lean_workbook_plus_12199
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:11:00.294299+00:00
-- url     : https://prove2.me/submissions/2205fbd3-6731-4a8b-9d78-b54a6968ef81

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ)
  (h₀ : 0 ≤ a)
  (h₁ : a ≤ 1) :
  a^2 * (1 - a) ≤ (4:ℝ) / 27 := by
  have hp := mul_nonneg (sq_nonneg (a-2/3)) (show 0 ≤ a+1/3 by linarith)
  nlinarith only [hp]
