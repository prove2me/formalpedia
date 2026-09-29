-- Prove2me | solution 1 for lean_workbook_plus_2204
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:43.658401+00:00
-- url     : https://prove2.me/submissions/6c932919-54e7-4075-9b82-b8e9e9e57b8a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * (1 - b) = 1 / 4) (hbc : b * (1 - c) = 1 / 4) (hca : c * (1 - a) = 1 / 4) : a = b ∧ b = c ∧ c = a := by
  intros
  grind
