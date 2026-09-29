-- Prove2me | solution 1 for lean_workbook_plus_56040
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:19:32.255776+00:00
-- url     : https://prove2.me/submissions/9dfbee4e-b438-4f61-81cd-59c19bb5b453

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000


theorem solution {x y : ℝ} (h : y ≥ 0) (h' : y * (y + 1) ≤ (x + 1) ^ 2) : y * (y - 1) ≤ x ^ 2 := by
  intros
  nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x - y)]
