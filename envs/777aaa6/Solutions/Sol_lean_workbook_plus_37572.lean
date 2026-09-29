-- Prove2me | solution 1 for lean_workbook_plus_37572
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:32.060014+00:00
-- url     : https://prove2.me/submissions/f7041be3-dd4c-44ea-8b2b-d5e00320ad82

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x + y + z = 1) (h₂ : x*y*z = 3) : y = (1 - x - z) ∧ z = (1 - x - y) := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
