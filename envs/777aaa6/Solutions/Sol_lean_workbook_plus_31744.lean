-- Prove2me | solution 1 for lean_workbook_plus_31744
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:39.412527+00:00
-- url     : https://prove2.me/submissions/617a4c95-54e6-471a-aca8-ad3a5f359c36

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a c : ℝ) (f : ℝ → ℝ) (hf: f = fun x ↦ c * (Real.sqrt ((2*a - 1)*x^4 + 4 - 2*a) / (3*x^2))) : a ∈ Set.Icc (1/2) 2 ∧ c > 0 → ∀ x > 0, f x = c * (Real.sqrt ((2*a - 1)*x^4 + 4 - 2*a) / (3*x^2)) := by
  (intros; simp_all)
