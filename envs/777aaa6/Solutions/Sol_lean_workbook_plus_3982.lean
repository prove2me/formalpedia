-- Prove2me | solution 1 for lean_workbook_plus_3982
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:43.415513+00:00
-- url     : https://prove2.me/submissions/6629e342-f172-4e30-9bef-1bf980cab2b4

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ↔ a * (a - b) ^ 2 + b * (b - c) ^ 2 + c * (c - a) ^ 2 ≥ 0 := by
  intros
  grind
