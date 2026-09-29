-- Prove2me | solution 1 for lean_workbook_plus_69921
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:46:09.790277+00:00
-- url     : https://prove2.me/submissions/5d748759-5f93-4941-8ea8-9851a3828c5d

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c : ℝ) : 27 * a ^ 2 * b ^ 2 * c ^ 2 ≥ (2 * b ^ 2 + 2 * c ^ 2 - a ^ 2) * (2 * c ^ 2 + 2 * a ^ 2 - b ^ 2) * (2 * a ^ 2 + 2 * b ^ 2 - c ^ 2) ↔ (b ^ 2 + c ^ 2 - 2 * a ^ 2) * (b ^ 2 - c ^ 2) ^ 2 + (c ^ 2 + a ^ 2 - 2 * b ^ 2) * (c ^ 2 - a ^ 2) ^ 2 + (a ^ 2 + b ^ 2 - 2 * c ^ 2) * (a ^ 2 - b ^ 2) ^ 2 ≥ 0 := by
  intros
  grind
