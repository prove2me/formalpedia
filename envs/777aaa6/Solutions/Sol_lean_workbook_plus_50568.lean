-- Prove2me | solution 1 for lean_workbook_plus_50568
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:54.403261+00:00
-- url     : https://prove2.me/submissions/3502d185-d96e-45f2-a954-228e255f9f9a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : 2 * (Real.sqrt x) ^ 3 + y ^ 3 ≥ 3 * (Real.sqrt x) ^ 2 * y ↔ (Real.sqrt x - y) ^ 2 * (2 * Real.sqrt x + y) ≥ 0 := by
  intros
  grind
