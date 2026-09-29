-- Prove2me | solution 1 for lean_workbook_plus_44040
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:02:15.175182+00:00
-- url     : https://prove2.me/submissions/c988715a-fbbd-4d99-bb12-1a0cb73c0a68

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxy : x < y) : x / y < (x + z) / (y + z) := by
  apply (div_lt_div_iff₀ hy (add_pos hy hz)).2
  nlinarith [mul_pos hz (sub_pos.mpr hxy)]
