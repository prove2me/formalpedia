-- Prove2me | solution 1 for lean_workbook_plus_34646
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:58.83616+00:00
-- url     : https://prove2.me/submissions/7355ef03-e670-4c0d-b180-da6f35a37c1b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a * b ≤ (1 / 2) * (a ^ 2 + b ^ 2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb])
