-- Prove2me | solution 1 for lean_workbook_plus_59333
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:43:48.663095+00:00
-- url     : https://prove2.me/submissions/03fbfc4e-8617-4594-befc-603f00fb25a6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c α β γ : ℝ) : a > 0 ∧ b > 0 ∧ c > 0 → α = a^2 / b / c ∧ β = b^2 / c / a ∧ γ = c^2 / a / b → a^2 / b / c + b^2 / c / a + c^2 / a / b ≤ α + β + γ := by
  (intros; simp_all)
