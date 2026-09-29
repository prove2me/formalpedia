-- Prove2me | solution 1 for lean_workbook_plus_2680
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:55.749044+00:00
-- url     : https://prove2.me/submissions/ccd554f9-c345-490f-ad3c-70ce46446c8e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℝ) (h₁ : 0 < b ∧ 0 < c) (h₂ : b ≤ 1 ∧ c ≤ 1) : 2 * b * c + 1 ≥ b + c := by
  (intros; nlinarith [sq_nonneg (b), sq_nonneg (c), sq_nonneg (b - c), sq_nonneg (b + c)])
