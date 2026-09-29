-- Prove2me | solution 1 for lean_workbook_plus_75534
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:22.651843+00:00
-- url     : https://prove2.me/submissions/e30d9ff1-339a-45d6-965f-6a3f772785d1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : (1 + a ^ 2) * (1 + a ^ 2 + b ^ 2) * (1 + a ^ 2 + b ^ 2 + c ^ 2) ≥ 16 * a * b * c ↔ (1 + a ^ 2) * (1 + a ^ 2 + b ^ 2) * c ^ 2 - 16 * a * b * c + (1 + a ^ 2) * (1 + a ^ 2 + b ^ 2) ^ 2 ≥ 0 := by
  intros
  grind
