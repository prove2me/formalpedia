-- Prove2me | solution 1 for lean_workbook_plus_14191
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:28.733643+00:00
-- url     : https://prove2.me/submissions/d4a66de9-7132-41d8-8cd8-f4d12b25e90d

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y : ℝ) (h : ∀ ε > 0, |x - y| < ε) : x = y := by
  by_contra hxy
  have hp : 0 < |x-y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  exact (lt_irrefl _ (h |x-y| hp))
