-- Prove2me | solution 1 for lean_workbook_plus_6400
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:31:36.45209+00:00
-- url     : https://prove2.me/submissions/dc3120ad-3bc1-4fd7-b845-7ec513e3855e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (p q a : ℂ)
  (h₀ : (3 * p * q - 1) = a * (p * q - p - q + 1)) :
  (a - 3) * p * q + a + 1 = a * (p + q) := by
  linear_combination -h₀
