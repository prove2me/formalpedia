-- Prove2me | solution 1 for lean_workbook_plus_27473
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:35.791544+00:00
-- url     : https://prove2.me/submissions/313b7c38-ea2e-4d8d-bd42-520fafd40c28

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (y s : ℝ)
  (h₀ : 0 < s - 940 + 1 / 4)
  (h₁ : 0 < s - 940 + 1 / 2)
  (h₂ : 0 < s - 940 + 1)
  (h₃ : s - 940 + 1 / 4 ≤ s)
  (h₄ : s - 940 + 1 / 2 ≤ s)
  (h₅ : s - 940 + 1 ≤ s)
  (h₆ : y = s - 940 + 1 / 2 + Real.sqrt (s - 940 + 1 / 4)) :
  y = s - 940 + 1 / 2 + Real.sqrt (s - 940 + 1 / 4) ∧ s ≥ 940 - 1 / 4 := by
  (intros; constructor <;> nlinarith [sq_nonneg (y), sq_nonneg (s), sq_nonneg (y - s), sq_nonneg (y + s)])
