-- Prove2me | solution 1 for lean_workbook_plus_8312
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:18:17.207494+00:00
-- url     : https://prove2.me/submissions/7b69d4de-7f04-4b41-bf2b-78fdb818cf97

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z a b c : ℝ) : a = y + z ∧ b = z + x ∧ c = x + y → x = (b + c - a) / 2 ∧ y = (a + c - b) / 2 ∧ z = (a + b - c) / 2 := by
  intros
  grind
