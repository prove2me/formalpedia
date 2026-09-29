-- Prove2me | solution 1 for lean_workbook_plus_14790
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:10.758842+00:00
-- url     : https://prove2.me/submissions/e0fdef90-8cec-4e30-ba16-f7ad90eff717

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (A : Set ℝ) (hA: A = {x : ℝ | ∀ y : ℝ, f (x * y) = x * f y}) : 1 ∈ A := by
  (intros; simp_all)
