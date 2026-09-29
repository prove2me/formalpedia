-- Prove2me | solution 1 for lean_workbook_plus_66024
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:05:56.396523+00:00
-- url     : https://prove2.me/submissions/c32c518f-cc25-4c82-9cd2-faf71572c782

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x a b : ℝ)
  (h₀ : 1 < a ∧ 1 < b)
  (h₁ : b / (b - 1) ≤ x ∧ x ≤ a / (a - 1))
  (h₂ : 0 < a ∧ 0 < b)
  (h₃ : b ≤ a)
  : (b / (b - 1) ≤ x ∧ x ≤ a / (a - 1)) ↔ b / (b - 1) ≤ x ∧ x ≤ a / (a - 1) := by
  norm_num
