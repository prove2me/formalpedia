-- Prove2me | solution 1 for lean_workbook_plus_6542
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:56.700092+00:00
-- url     : https://prove2.me/submissions/77b40686-e48c-4fe5-82be-9f2e74e0d2ad

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 1 / 9 * (a + b + c) ^ 3 + 2 * (a ^ 3 + b ^ 3 + c ^ 3) ↔ 0 ≤ (5 * a + 5 * b - c) * (a - b) ^ 2 + (5 * b + 5 * c - a) * (b - c) ^ 2 + (5 * c + 5 * a - b) * (c - a) ^ 2 := by
  intros
  grind
