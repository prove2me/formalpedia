-- Prove2me | solution 1 for lean_workbook_plus_81578
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:38:08.426631+00:00
-- url     : https://prove2.me/submissions/74b31e72-52c9-49f3-8cda-9a753c486068

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (Q T : ℝ → ℝ) (h₁ : ∀ x, Q x = (1 + (2 * x - 1) * T (x ^ 2 - x)) / 2) : ∀ x, Q x = (1 + (2 * x - 1) * T (x ^ 2 - x)) / 2 := by
  (intros; simp_all)
