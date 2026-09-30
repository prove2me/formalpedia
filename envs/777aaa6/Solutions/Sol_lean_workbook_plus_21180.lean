-- Prove2me | solution 1 for lean_workbook_plus_21180
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:27:40.010344+00:00
-- url     : https://prove2.me/submissions/091f8c97-a162-4a99-81a9-8709f1f59e37

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf : ∀ x y, f (2 * x * y) = f x + f y) : f 2 = 7 → f 1 = 7 := by
  intro h2
  have h0 := hf 0 2
  norm_num at h0
  linarith
