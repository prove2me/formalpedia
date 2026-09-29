-- Prove2me | solution 1 for lean_workbook_plus_25802
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:36:02.557199+00:00
-- url     : https://prove2.me/submissions/c13d9345-817b-4d50-9f85-6e6687d01a55

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => x) : ∀ x, f x = x := by
  (intros; simp_all)
