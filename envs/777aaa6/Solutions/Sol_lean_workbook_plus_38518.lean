-- Prove2me | solution 1 for lean_workbook_plus_38518
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:59:40.288794+00:00
-- url     : https://prove2.me/submissions/159213c1-597e-40f6-810a-a20f4fad4009

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (f g : ℝ → ℝ) (f_def : ∀ x, f x = 4 * x + 3) (g_def : ∀ x, g x = (x + 1) / 4) : g (f (g (f 42))) = 44 := by
  simp only [f_def, g_def]
  norm_num
