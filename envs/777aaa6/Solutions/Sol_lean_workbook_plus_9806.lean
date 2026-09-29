-- Prove2me | solution 1 for lean_workbook_plus_9806
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:13:20.671845+00:00
-- url     : https://prove2.me/submissions/15b5524d-52d3-469b-a5d3-0d08e0da67e6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : 3 * x ^ 2 - 5 * x - 2 = 0 ↔ x = 2 ∨ x = -1/3 := by
  intros
  grind
