-- Prove2me | solution 1 for lean_workbook_plus_20307
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:19.24415+00:00
-- url     : https://prove2.me/submissions/485c9b22-ff7b-4c4e-9c7e-a759aaea8f12

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x / (1 + x ^ 2) ≤ 1 / 2 := by
  apply (div_le_iff₀ (show 0<1+x^2 by positivity)).2
  nlinarith [sq_nonneg (x-1)]
