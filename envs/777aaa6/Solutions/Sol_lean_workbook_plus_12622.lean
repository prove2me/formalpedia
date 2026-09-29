-- Prove2me | solution 1 for lean_workbook_plus_12622
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:40:55.594644+00:00
-- url     : https://prove2.me/submissions/222863ed-a977-4bca-997f-54b892a8561f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :
  1 / 2 * ((Real.sqrt 2 / 2)^2 * (-(Real.sqrt 2 / 2) - 0)^2 + (-(Real.sqrt 2 / 2))^2 * (0 - (Real.sqrt 2 / 2))^2) = 1 / 4 := by
  intros
  grind
