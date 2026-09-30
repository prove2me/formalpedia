-- Prove2me | solution 2 for lean_workbook_plus_67558
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:48.308851+00:00
-- url     : https://prove2.me/submissions/9fd594bd-68d4-4e9b-8ca8-5c3eafd375f5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h1 : 0 < a ∧ 0 < b) (h2 : a ≤ 2 * b) (h3 : 2 * b ≤ 4 * a) :
  4 * a * b ≤ 2 * (a ^ 2 + b ^ 2) ∧ 2 * (a ^ 2 + b ^ 2) ≤ 5 * a * b := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
