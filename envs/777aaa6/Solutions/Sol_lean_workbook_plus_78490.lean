-- Prove2me | solution 1 for lean_workbook_plus_78490
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:25:39.175203+00:00
-- url     : https://prove2.me/submissions/41b430aa-1efa-4bd6-8051-995d003f4ab3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (a_n : ℝ) (α : ℝ) (β : ℝ) (h₁ : α = (3 + Real.sqrt 5) / 2) (h₂ : β = (3 - Real.sqrt 5) / 2) (h₃ : a_n = α^(2^(n - 1)) + β^(2^(n - 1))) : a_n = α^(2^(n - 1)) + β^(2^(n - 1)) := by
  (intros; simp_all)
