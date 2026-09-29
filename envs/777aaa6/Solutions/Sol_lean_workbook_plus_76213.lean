-- Prove2me | solution 1 for lean_workbook_plus_76213
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:24:56.952007+00:00
-- url     : https://prove2.me/submissions/e1fc7313-7a31-450f-ae5c-ed3b3430766a

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (f : ℝ → ℝ) (hf: f (1 / 2) = f (1 / 4) ∨ f (1 / 2) = f (3 / 4)) : ¬ Function.Injective f := by
  intro hinj
  rcases hf with h | h
  · have := hinj h; norm_num at this
  · have := hinj h; norm_num at this
