-- Prove2me | solution 1 for lean_workbook_plus_46871
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:36:38.919519+00:00
-- url     : https://prove2.me/submissions/ee68902a-72f7-4c2e-97b1-0d186a887e63

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a b c : ℝ, a + b + c = 0 → (a^7 + b^7 + c^7) / 7 = (a^5 + b^5 + c^5) / 5 * (a^2 + b^2 + c^2) / 2 := by
  intro a b c
  intros
  grind
