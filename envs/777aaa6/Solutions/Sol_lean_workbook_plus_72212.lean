-- Prove2me | solution 1 for lean_workbook_plus_72212
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:20:31.919871+00:00
-- url     : https://prove2.me/submissions/935ca5e6-c92c-4a5f-9b07-15e0745f28a5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => (x^3 - 9*x)/(2*(1-x^2))) : ∀ x, f x = (x^3 - 9*x)/(2*(1-x^2)) := by
  (intros; simp_all)
