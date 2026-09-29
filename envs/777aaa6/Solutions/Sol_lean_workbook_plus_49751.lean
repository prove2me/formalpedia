-- Prove2me | solution 1 for lean_workbook_plus_49751
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:21:27.317288+00:00
-- url     : https://prove2.me/submissions/da3288af-10ce-424e-8980-8d3c74e68f2d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ)
  (h₀ : ∀ x, x ≠ 1 → f x = (2 * x^2 - 1) / (1 - x^4))
  : ∀ x, x ≠ 1 → f x = (2 * x^2 - 1) / (1 - x^4) := by
  (intros; simp_all)
