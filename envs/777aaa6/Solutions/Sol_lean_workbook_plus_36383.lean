-- Prove2me | solution 1 for lean_workbook_plus_36383
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:50:01.573899+00:00
-- url     : https://prove2.me/submissions/c390e101-0151-4222-876d-8078bc2328e1

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (α : ZMod 5) (hα : α^5 + 4*α + 3 = 0) : False := by
  exact (by decide : ∀ z : ZMod 5, z^5+4*z+3 ≠ 0) α hα
