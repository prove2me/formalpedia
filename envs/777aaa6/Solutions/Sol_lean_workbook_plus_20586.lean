-- Prove2me | solution 1 for lean_workbook_plus_20586
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:41.637523+00:00
-- url     : https://prove2.me/submissions/c9f19156-b621-4a21-b5a4-c76e1b4353d5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x ↦ 0) : ∀ x y, x^2*y^2 * (f (x+y) - f x - f y) = 3 * (x+y) * f x * f y := by
  (intros; simp_all)
