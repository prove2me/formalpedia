-- Prove2me | solution 1 for lean_workbook_plus_21277
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:27:24.216807+00:00
-- url     : https://prove2.me/submissions/2715b9c9-e176-48b8-bc47-fc5b4252b3a4

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (f : ℝ → ℝ) (hf : ∀ a, f a + f (-a) = 0) : ∀ a, f a = -f (-a) := by
  intro a
  linarith [hf a]
