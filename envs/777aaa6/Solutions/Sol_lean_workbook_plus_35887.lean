-- Prove2me | solution 1 for lean_workbook_plus_35887
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:52.136419+00:00
-- url     : https://prove2.me/submissions/407f15f8-01e3-421d-a15e-9aa23372e65f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {a b c x y z A B C : ℂ} (ha : A = a * x + b * y + c * z) (hb : B = a * y + b * z + c * x) (hc : C = a * z + b * x + c * y) : (a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c) * (x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z) = A ^ 3 + B ^ 3 + C ^ 3 - 3 * A * B * C := by
  rw [ha,hb,hc]
  ring
