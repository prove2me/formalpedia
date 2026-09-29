-- Prove2me | solution 1 for lean_workbook_plus_6009
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:02.552866+00:00
-- url     : https://prove2.me/submissions/b453adb3-c4f8-4b20-a136-8db5d3fe0071

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b c: ℝ) : a * b + b * c + c * a ≥ -1 / 2 ↔ 2 * (a * b + b * c + c * a) + 1 ≥ 0 := by
  intros
  grind
