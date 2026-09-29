-- Prove2me | solution 1 for lean_workbook_plus_13141
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:30.628644+00:00
-- url     : https://prove2.me/submissions/f8244e37-ea92-4ffd-b7cb-d53e712aeb78

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ)
  (h₀ : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0)
  (h₁ : a + b + c = 1) :
  1 / (a * b * c * (a + b + c)) * (a + b + c) = 1 / (a * b * c) := by
  (intros; simp_all)
