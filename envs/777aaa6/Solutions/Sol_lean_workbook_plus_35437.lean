-- Prove2me | solution 1 for lean_workbook_plus_35437
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:31.154797+00:00
-- url     : https://prove2.me/submissions/07c887b2-9529-4177-b681-4e57a9271739

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c k : ℝ) (ha : a^2 + b^2 + c^2 + a * b * c = 4) (hb : 0 < k) : a^2 + k * b + k * c + a * b * c ≤ 4 + k^2 / 2 := by
  nlinarith [sq_nonneg (b-k/2),sq_nonneg (c-k/2)]
