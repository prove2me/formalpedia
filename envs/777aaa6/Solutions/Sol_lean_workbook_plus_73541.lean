-- Prove2me | solution 1 for lean_workbook_plus_73541
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:59.820683+00:00
-- url     : https://prove2.me/submissions/88d76326-12a0-4c7a-a8c3-5dba2076b77d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a + b > 0)
  (h₂ : 2 * a ≤ 3 * b) :
  a / (a + b) ≤ 3 / 5 := by
  (intros; field_simp; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
