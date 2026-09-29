-- Prove2me | solution 1 for lean_workbook_plus_12308
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:37.025497+00:00
-- url     : https://prove2.me/submissions/4f86ac3e-f582-412d-ae0b-b85ca922d606

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ)
  (h₀ : x + (7 - x^2)^2 = 11)
  (h₁ : x^4 - 14 * x^2 + x + 38 = 0) :
  x = 2 ∨ x^3 + 2 * x^2 - 10 * x - 19 = 0 := by
  intros
  grind
