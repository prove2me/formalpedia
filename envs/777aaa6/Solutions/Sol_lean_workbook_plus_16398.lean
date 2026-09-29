-- Prove2me | solution 1 for lean_workbook_plus_16398
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:19:13.022083+00:00
-- url     : https://prove2.me/submissions/d279b738-3e07-4211-b879-d967a25e850f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : ∀ c : ℝ, 0 < c ∧ c < 1 → c^2 + (1 - c)^2 < 1 := by
  intro c hc
  nlinarith [mul_pos hc.1 (by linarith : 0 < 1-c)]
