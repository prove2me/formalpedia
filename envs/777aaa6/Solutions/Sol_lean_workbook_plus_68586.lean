-- Prove2me | solution 1 for lean_workbook_plus_68586
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:01.534753+00:00
-- url     : https://prove2.me/submissions/3f544769-dc6e-43c5-a1e9-865e76fa97c4

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : x = 1.98) : 5 * x ^ 4 + 7 * x ^ 3 + 8 * x ^ 2 + 9 * x + 10 = 190.3676248 := by
  subst x
  norm_num
