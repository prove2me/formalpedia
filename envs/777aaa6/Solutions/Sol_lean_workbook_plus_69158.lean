-- Prove2me | solution 1 for lean_workbook_plus_69158
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:41:10.033852+00:00
-- url     : https://prove2.me/submissions/62449d09-818e-4e69-8c5b-eddd3d947653

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 ↔ 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 := by
  intro a b c
  intros
  grind
