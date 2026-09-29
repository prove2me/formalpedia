-- Prove2me | solution 1 for lean_workbook_plus_30818
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:54:57.570705+00:00
-- url     : https://prove2.me/submissions/0039786a-a5ef-4626-878f-d075cb3b6f69

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (y : ℝ) (h : y > 0) : (y + 1) ^ 7 - 2 * (y + 1) ^ 5 + 10 * (y + 1) ^ 2 - 1 > 0 := by
  have he : (y+1)^7-2*(y+1)^5+10*(y+1)^2-1 = y^7+7*y^6+19*y^5+25*y^4+15*y^3+11*y^2+17*y+8 := by ring
  rw [he]
  positivity
