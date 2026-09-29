-- Prove2me | solution 1 for lean_workbook_plus_46203
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:51:51.521434+00:00
-- url     : https://prove2.me/submissions/469aa2c2-62b7-4bfb-9f18-fde3b1bac5bb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution :
  ∑' k : ℕ, (1 / 4)^k * (Real.sqrt 5 / 4) = (Real.sqrt 5 / 3) := by
  rw [tsum_mul_right,tsum_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)| < 1)]
  ring
