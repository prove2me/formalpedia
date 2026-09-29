-- Prove2me | solution 1 for lean_workbook_plus_74029
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:49:39.908457+00:00
-- url     : https://prove2.me/submissions/e76c201e-7893-4df3-91e8-31ca15e8a357

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a : ℝ) : (6 + Real.sqrt (36 - 4 * 3 * (-9 + 4 * a))) / (2 * 3) = (6 + Real.sqrt (144 - 48 * a)) / 6 := by
  intros
  grind
