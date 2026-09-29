-- Prove2me | solution 1 for lean_workbook_plus_27379
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:14:38.330085+00:00
-- url     : https://prove2.me/submissions/b1cd5361-181f-4b3f-807a-abff765b64d1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2): 2 * (a + b) ^ 2 ≤ 9 * a * b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
