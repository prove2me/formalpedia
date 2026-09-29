-- Prove2me | solution 1 for lean_workbook_plus_15193
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:13:07.720439+00:00
-- url     : https://prove2.me/submissions/22046fcf-4ffa-4aeb-b7cf-03d76c3b52b4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => x^3) : ∀ x, f x = x^3 := by
  (intros; simp_all)
