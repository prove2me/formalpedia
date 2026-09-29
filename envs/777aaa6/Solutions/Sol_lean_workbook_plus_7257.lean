-- Prove2me | solution 1 for lean_workbook_plus_7257
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:51.423022+00:00
-- url     : https://prove2.me/submissions/12ff4c8a-36fc-4db7-9781-1d3db587b87f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution {x y z : ℝ} (h : x + y + z = 2) : 2 * (x * y + y * z + z * x) * (1 + 6 * x * y * z) - 25 * x * y * z = y * (2 * y - 1) ^ 2 * (x - z) ^ 2 + z * (2 * z - 1) ^ 2 * (x - y) ^ 2 + x * (2 * x - 1) ^ 2 * (y - z) ^ 2 := by
  have hx : x = 2-y-z := by linarith
  rw [hx]
  ring
