-- Prove2me | solution 1 for lean_workbook_plus_57377
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:29.011241+00:00
-- url     : https://prove2.me/submissions/e2275fa0-7273-4510-9097-d1f095089eb2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ x y z a b c : ℝ, x = a + b → y = a + c → z = b + c → x^2 + y^2 + z^2 = a^2 + b^2 + c^2 + (a + b + c)^2 := by
  intro x y z a b c
  intros
  grind
