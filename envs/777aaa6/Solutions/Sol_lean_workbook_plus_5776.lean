-- Prove2me | solution 1 for lean_workbook_plus_5776
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:18:15.237266+00:00
-- url     : https://prove2.me/submissions/ba29df88-bea9-4c68-8a57-39dedbb85422

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℂ) (h : x * y * z = (1 - x) * (1 - y) * (1 - z)) :
  2 * x * y * z + x + y + z = x * y + y * z + z * x + 1 := by
  linear_combination h
