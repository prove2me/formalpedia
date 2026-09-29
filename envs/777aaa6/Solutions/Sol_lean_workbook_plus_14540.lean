-- Prove2me | solution 1 for lean_workbook_plus_14540
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:39.033388+00:00
-- url     : https://prove2.me/submissions/8a2978a3-8b2f-43d3-ab41-137e6e390541

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y : ℝ) : |y| - |x| ≤ |x - y| := by
  intros
  grind
