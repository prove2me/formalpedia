-- Prove2me | solution 1 for lean_workbook_plus_26556
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:41:50.773883+00:00
-- url     : https://prove2.me/submissions/874b0e86-0df2-433f-b662-18b733f0556e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m n a b c : ℤ)
  (h₀ : 0 < m ∧ 0 < n ∧ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c)
  (h₁ : m^2 + n^2 + a^2 + b^2 + c^2 = 1989)
  (h₂ : m^2 + n^2 + a + b + c = 19)
  (h₃ : m^2 + a^2 + b^2 + c^2 = 44)
  (h₄ : n^2 + a^2 + b^2 + c^2 = 25) :
  m^2 = 81 ∧ n^2 = 36 := by
  (intros; omega)
