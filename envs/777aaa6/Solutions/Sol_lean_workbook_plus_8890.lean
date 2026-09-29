-- Prove2me | solution 1 for lean_workbook_plus_8890
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:51.323114+00:00
-- url     : https://prove2.me/submissions/88a624a5-9d4a-4d62-8be4-54f420c425d1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c x y z : ℝ) : a + b - c = x ∧ b + c - a = y ∧ c + a - b = z → (x + y) / 2 = b ∧ (z + y) / 2 = c ∧ (x + z) / 2 = a := by
  intros
  grind
