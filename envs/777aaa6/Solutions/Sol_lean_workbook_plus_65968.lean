-- Prove2me | solution 1 for lean_workbook_plus_65968
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:27:20.776417+00:00
-- url     : https://prove2.me/submissions/b0043ba3-a173-4f6f-898d-2eb49eb9f0a4

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ) : 5 * (x ^ 2 + y ^ 2) ^ 2 ≤ 4 + (x + y) ^ 4 ↔ x ^ 4 + y ^ 4 + x ^ 2 * y ^ 2 ≤ 1 + x ^ 3 * y + x * y ^ 3 := by
  constructor <;> intro h <;> nlinarith
