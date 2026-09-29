-- Prove2me | solution 1 for lean_workbook_plus_48076
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:25.352076+00:00
-- url     : https://prove2.me/submissions/71b57e26-e5ae-4631-a6ee-50c138d71640

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 3 ≤ a) (hb : 3 ≤ b) (h : a^2 ≥ 3 * b) : 48 * a^2 + 12 * b^2 + 255 ≥ 104 * a + 101 * a + 20 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
