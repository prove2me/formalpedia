-- Prove2me | solution 1 for lean_workbook_plus_38909
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:20:06.943337+00:00
-- url     : https://prove2.me/submissions/c676500e-c28c-4449-ac7f-3cebb50cad98

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : 0 < x) : 2 * Int.floor x ≤ Int.floor (2 * x) := by
  apply Int.le_floor.mpr
  push_cast
  nlinarith [Int.floor_le x]
