-- Prove2me | solution 1 for lean_workbook_plus_29475
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:04:23.024677+00:00
-- url     : https://prove2.me/submissions/60c85472-edf4-420b-aab2-c8960a854745

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => x^4) : ∀ x, f x = x^4 := by
  (intros; simp_all)
