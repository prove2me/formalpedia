-- Prove2me | solution 1 for lean_workbook_plus_57526
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:20.814273+00:00
-- url     : https://prove2.me/submissions/a2527252-b1df-4025-874a-d6f0f6dda63b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℚ)
  (h₀ : 9 * x + 4 * y = 1)
  (h₁ : 8 * x + 7 * y = 1) :
  x = 3 / 31 ∧ y = 1 / 31 := by
  intros
  grind
