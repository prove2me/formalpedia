-- Prove2me | solution 1 for lean_workbook_plus_16524
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:20:25.196457+00:00
-- url     : https://prove2.me/submissions/5098c82b-c0f9-4d20-87ad-6440ccd2f6cd

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) ^ 3 + (x + z) ^ 3 + (y + z) ^ 3 + 8 * x * y * z ≥ 4 * (x + y) * (x + z) * (y + z) ↔ 2 * (x ^ 3 + y ^ 3 + z ^ 3) ≥ x ^ 2 * (y + z) + y ^ 2 * (x + z) + z ^ 2 * (x + y) := by
  constructor <;> intro h <;> nlinarith
