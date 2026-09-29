-- Prove2me | solution 1 for lean_workbook_plus_1895
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:20.177999+00:00
-- url     : https://prove2.me/submissions/0e191d8c-308e-4031-bad8-c702e8513f4c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a^2 + 2 * b ≥ a^2 + 2 * a + 1) :
  2 * b ≥ 2 * a + 1 := by
  (intros; linarith)
