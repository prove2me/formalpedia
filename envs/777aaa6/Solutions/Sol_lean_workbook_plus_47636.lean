-- Prove2me | solution 1 for lean_workbook_plus_47636
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:07:23.1518+00:00
-- url     : https://prove2.me/submissions/b69b9b80-84e6-4e64-9042-dc73f6564dd1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : ↑⌊x⌋ ≤ x ∧ x < ↑⌊x⌋ + 1 := by
  intros
  exact Int.floor_eq_iff.mp rfl
