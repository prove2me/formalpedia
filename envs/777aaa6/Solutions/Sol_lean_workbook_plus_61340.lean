-- Prove2me | solution 1 for lean_workbook_plus_61340
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:56.530996+00:00
-- url     : https://prove2.me/submissions/b6c488f3-f6cd-40a6-ad84-6e26cf99c2d3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x : ℝ) : max x 0 = if x ≤ 0 then 0 else x := by
  intros
  grind
