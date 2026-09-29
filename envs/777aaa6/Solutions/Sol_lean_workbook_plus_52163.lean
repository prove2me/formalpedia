-- Prove2me | solution 1 for lean_workbook_plus_52163
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:15:33.384393+00:00
-- url     : https://prove2.me/submissions/9f637986-6369-44d5-a1f5-092facbd5871

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∃ a b : ℤ, 22*a + 6*b = 2 := by
  exact ⟨-1,4,by norm_num⟩
