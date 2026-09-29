-- Prove2me | solution 1 for lean_workbook_plus_74691
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:21:32.683065+00:00
-- url     : https://prove2.me/submissions/212f579b-c66f-4dcd-8a2f-fe65588aac69

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) : 27 * (3 * a ^ 3 + 3 * b ^ 3 + 3 * c ^ 3 + 7 * a * b * c) ≥ 16 * (a + b + c) ^ 3 ↔ 65 * (a ^ 3 + b ^ 3 + c ^ 3) + 93 * a * b * c ≥ 48 * (a * b * (a + b) + b * c * (b + c) + c * a * (c + a)) := by
  constructor <;> intro h <;> nlinarith
