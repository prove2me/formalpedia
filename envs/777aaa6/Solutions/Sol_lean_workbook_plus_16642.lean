-- Prove2me | solution 1 for lean_workbook_plus_16642
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:13.631352+00:00
-- url     : https://prove2.me/submissions/94ad94c1-f9d4-499a-92e4-8bd2f2a66bb9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / (a + b + c - 1) + (b + c) / a + (c + a) / b + (a + b) / c ≥ 2 + 1 / a + 1 / b + 1 / c ↔ 1 / (a + b + c - 1) + (a + b + c - 1) * (1 / a + 1 / b + 1 / c) ≥ 5 := by
  intros
  grind
