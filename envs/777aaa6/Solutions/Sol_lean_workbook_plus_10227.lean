-- Prove2me | solution 1 for lean_workbook_plus_10227
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:55:39.664764+00:00
-- url     : https://prove2.me/submissions/024b7668-e612-45ff-bc51-a50d9789d02f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ) (hx : x = 1 / 3) (hy : y = 1 / 3) (hz : z = 1 / 3) : (4 / (x + y) ^ 2 + 4 / (x + z) ^ 2 + 4 / (y + z) ^ 2) ≥ 27 / (x + y + z) ^ 2 := by
  rw [hx,hy,hz]
  field_simp
  norm_num
