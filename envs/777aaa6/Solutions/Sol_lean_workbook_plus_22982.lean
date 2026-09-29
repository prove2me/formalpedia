-- Prove2me | solution 1 for lean_workbook_plus_22982
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:38:57.787472+00:00
-- url     : https://prove2.me/submissions/92f2752d-06c8-481c-a793-ffcf8a16a217

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (x y z : ℝ) (h : x * y * z + 1 / (x * y * z) - 2 = 0) : (x * y * z) ^ 2 - 2 * (x * y * z) + 1 = 0 := by
  intros
  grind
