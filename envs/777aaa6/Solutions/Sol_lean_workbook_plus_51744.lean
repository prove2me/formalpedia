-- Prove2me | solution 1 for lean_workbook_plus_51744
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:06:08.243276+00:00
-- url     : https://prove2.me/submissions/1893b681-5f5a-4ad0-b9f4-36ded96cab0d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ)
  (h₀ : ∀ x, (¬ ∃ a : ℤ, x = a) → (f x = 1 ∨ f x = -1)) :
  ∀ x, (¬ ∃ a : ℤ, x = a) → f x = 1 ∨ f x = -1 := by
  norm_num
