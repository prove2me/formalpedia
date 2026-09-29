-- Prove2me | solution 1 for lean_workbook_plus_70762
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:47.405425+00:00
-- url     : https://prove2.me/submissions/27bdc83e-d84f-42c7-b35a-51c39a6e4bb7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c d : ℝ) : a = b ∧ c = d ↔ a + c = b + d ∧ a - c = b - d := by
  intros
  grind
