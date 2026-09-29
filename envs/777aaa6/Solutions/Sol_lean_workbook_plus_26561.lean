-- Prove2me | solution 1 for lean_workbook_plus_26561
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:58.904484+00:00
-- url     : https://prove2.me/submissions/f1d991d3-6bec-433c-814e-16003cd9dd88

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : a+b = 5/6 ∧ b+c = 7/10 ∧ c+a = 8/15 ↔ a = 1/3 ∧ b = 1/2 ∧ c = 1/5 := by
  intros
  grind
