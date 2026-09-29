-- Prove2me | solution 1 for lean_workbook_plus_8957
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:58.671653+00:00
-- url     : https://prove2.me/submissions/2cf0086d-d9f9-4b06-9d50-89f6b3eb79fa

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c k : ℝ) (h₁ : k = a + b + c) (h₂ : a + b + c ≠ 0) : a / k + b / k + c / k = 1 := by
  intros
  grind
