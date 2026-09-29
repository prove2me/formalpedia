-- Prove2me | solution 1 for lean_workbook_plus_63581
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:08:08.367839+00:00
-- url     : https://prove2.me/submissions/38956659-5aba-4baf-950e-a67697a12b96

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : 1 / a = x)
  (h₂ : 1 / b = y)
  (h₃ : 1 / c = z)
  (h₄ : a < b)
  (h₅ : b < c)
  (h₆ : 0 < x ∧ 0 < y ∧ 0 < z)
  (h₇ : x < y)
  (h₈ : y < z)
  (h₉ : 2 * y = x + z) :
  x + z = 2 * y := by
  (intros; simp_all)
