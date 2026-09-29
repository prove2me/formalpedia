-- Prove2me | solution 1 for lean_workbook_plus_19894
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:59.368143+00:00
-- url     : https://prove2.me/submissions/ec74541d-1723-4c99-a1d0-aa1b2c788237

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z w : ℝ) (h : x + y + z + w = 2) :
  (x + z) * (y + w) ≤ 1 := by
  nlinarith [sq_nonneg (x+z-(y+w)), sq_nonneg (x+y+z+w-2)]
