-- Prove2me | solution 1 for lean_workbook_plus_14162
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:17.595298+00:00
-- url     : https://prove2.me/submissions/10466de0-64e5-4f6a-bc82-cf2fbd7a46cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (f : ℝ → ℝ) (hf: f ((x^2+1)*y) = (x^2+1)*f y) : f ((x^2+1)*y) = (x^2+1)*f y := by
  (intros; simp_all)
