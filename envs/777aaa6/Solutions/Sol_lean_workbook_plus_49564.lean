-- Prove2me | solution 1 for lean_workbook_plus_49564
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:24:01.867945+00:00
-- url     : https://prove2.me/submissions/13d5fcea-c04b-48d9-849e-4d11131f6bf8

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : a^2 + b^2 + c^2 + 3 ≥ 2 * (a + b + c) ↔ (a - 1)^2 + (b - 1)^2 + (c - 1)^2 ≥ 0 := by
  constructor <;> intro h <;> nlinarith
