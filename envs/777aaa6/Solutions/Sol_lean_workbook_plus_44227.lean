-- Prove2me | solution 1 for lean_workbook_plus_44227
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:20.438513+00:00
-- url     : https://prove2.me/submissions/704b57dc-6d2b-4a7e-9f62-3df4ca175a15

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a < b) : a < (a + b) / 2 ∧ (a + b) / 2 < b := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
