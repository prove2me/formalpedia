-- Prove2me | solution 1 for lean_workbook_plus_8520
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:47.36653+00:00
-- url     : https://prove2.me/submissions/6a3ee6c5-1161-42f8-b4b8-67860adc578a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (hf : ∀ x ≠ 0, 3 * f x - 5 * x * f (1 / x) = x - 7) : f 2010 = 4021 := by
  intros
  grind
