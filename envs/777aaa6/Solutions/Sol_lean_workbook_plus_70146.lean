-- Prove2me | solution 1 for lean_workbook_plus_70146
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:10:15.992102+00:00
-- url     : https://prove2.me/submissions/5cc7dce0-687a-4b14-acda-bcd0b308b6c2

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b c : ℝ} :
  a ^ 4 * b ^ 2 + a ^ 4 * c ^ 2 + b ^ 4 * c ^ 2 + b ^ 4 * a ^ 2 + c ^ 4 * a ^ 2 + c ^ 4 * b ^ 2 ≥ a ^ 4 * b * c + a ^ 4 * c * b + b ^ 4 * c * a + b ^ 4 * a * c + c ^ 4 * a * b + c ^ 4 * b * a ↔ a ^ 4 * (b - c) ^ 2 + b ^ 4 * (c - a) ^ 2 + c ^ 4 * (a - b) ^ 2 ≥ 0 := by
  intros
  grind
