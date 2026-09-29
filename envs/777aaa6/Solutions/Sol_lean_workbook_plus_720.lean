-- Prove2me | solution 1 for lean_workbook_plus_720
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:56:36.003929+00:00
-- url     : https://prove2.me/submissions/38e9c731-2cfd-4021-846b-feef6afe5df6

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (x : ℝ) : x^3 - 9*x^2 + 27*x - 27 = 0 ↔ x = 3 := by
  have he : x^3-9*x^2+27*x-27 = (x-3)^3 := by ring
  rw [he, pow_eq_zero_iff (by decide : 3 ≠ 0), sub_eq_zero]
