-- Prove2me | solution 1 for lean_workbook_plus_70390
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:26.263174+00:00
-- url     : https://prove2.me/submissions/2a9559b4-b728-4423-b96e-d0a4147df22c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (f : ℝ → ℝ) (hf: f = fun x ↦ x^2 + a) : (∀ x, f x = x^2 + a) ∧ (∀ x, f x = x^2 + a) := by
  (intros; simp_all)
