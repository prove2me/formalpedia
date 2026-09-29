-- Prove2me | solution 1 for lean_workbook_plus_10183
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:53:15.365178+00:00
-- url     : https://prove2.me/submissions/88fb01c8-f406-4756-95f3-39fbe4a633d0

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ y : ℤ, y % 4 = 3 → (y^3 + 27) % 4 = 2 := by
  intro y h
  have hm : y ≡ 3 [ZMOD 4] := by simpa [Int.ModEq] using h
  have hp := (hm.pow 3).add_right 27
  norm_num [Int.ModEq] at hp
  exact hp
