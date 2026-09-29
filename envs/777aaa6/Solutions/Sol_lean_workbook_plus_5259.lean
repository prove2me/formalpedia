-- Prove2me | solution 1 for lean_workbook_plus_5259
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:07:30.28079+00:00
-- url     : https://prove2.me/submissions/313aaeb2-90ae-483a-9024-a2c33e433c19

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) :
  (x - 2)^2 + 3 ≥ 3 ∧ (y + 1)^2 + 5 ≥ 5 := by
  (intros; constructor <;> nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
