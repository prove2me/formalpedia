-- Prove2me | solution 1 for lean_workbook_plus_62589
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:25.76444+00:00
-- url     : https://prove2.me/submissions/4af72f05-92ad-4d28-a7b4-81efec734fd6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 3) : 27 ≥ a^3 + b^3 + 3 * a * b ∧ a^3 + b^3 + 3 * a * b ≥ 27 / 2 := by
  (intros; constructor <;> nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_nonneg ha hb])
