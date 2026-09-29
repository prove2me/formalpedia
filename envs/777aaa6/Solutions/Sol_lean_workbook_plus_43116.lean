-- Prove2me | solution 1 for lean_workbook_plus_43116
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:16:34.755803+00:00
-- url     : https://prove2.me/submissions/d6e523ae-85a8-4041-9ece-55b2dd8918c7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (N : Type) [AddCommMonoid N] [Mul N] (h₁ : ∀ a b c : N, (a + b) * c = a * c + b * c) (h₂ : ∀ a b c : N, a * (b + c) = (a * b) * c) : 5 * 5 = 160 → 7 * 7 = 896 := by
  norm_num
