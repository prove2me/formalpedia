-- Prove2me | solution 1 for lean_workbook_plus_14763
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:12:41.13063+00:00
-- url     : https://prove2.me/submissions/1843ec0c-15c5-44f5-bcab-417dfacad19d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ → ℝ) (hf : ∀ x y, f (x + y) = f (x*y) - f x + f (-y)) : f (-1) = 5 → f 2022 = 5 := by
  intro h
  have h1 := hf (-1) 0
  have h2 := hf 2022 0
  simp only [add_zero,mul_zero,neg_zero] at h1 h2
  linarith
