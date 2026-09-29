-- Prove2me | solution 1 for lean_workbook_plus_71187
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:15.905615+00:00
-- url     : https://prove2.me/submissions/5d0e0e84-24bb-41a7-a2c4-8bbbfa12c04d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) (hb : 0 < b ∧ b ≤ 1) (hc : 0 < c ∧ c ≤ 1) : 2 * b * c + 1 ≥ b + c := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
