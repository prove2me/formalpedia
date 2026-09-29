-- Prove2me | solution 1 for lean_workbook_plus_34191
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:11:21.945609+00:00
-- url     : https://prove2.me/submissions/2b0adb18-42a7-4080-8b8b-fb29b25f79ec

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution (n : ℕ) (hn : 1 ≤ n) : 15 ∣ 2 ^ (4 * n) - 1 := by
  simpa [pow_mul] using Nat.sub_one_dvd_pow_sub_one 16 n
