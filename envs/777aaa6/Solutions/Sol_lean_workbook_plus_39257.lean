-- Prove2me | solution 1 for lean_workbook_plus_39257
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:54:38.922405+00:00
-- url     : https://prove2.me/submissions/e141ee22-b952-44f7-a3ac-b05ecf59867b

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) : (a - b) ^ 2 + (c - 1) ^ 2 + 2 * c * (a - 1) * (b - 1) ≥ 0 ↔ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c + 1 ≥ 2 * (a * b + b * c + a * c) := by
  constructor <;> intro h <;> nlinarith
