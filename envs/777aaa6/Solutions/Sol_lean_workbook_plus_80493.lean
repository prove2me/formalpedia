-- Prove2me | solution 1 for lean_workbook_plus_80493
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:00:53.187353+00:00
-- url     : https://prove2.me/submissions/e55fadb9-5bbc-4a35-9bc3-ae4fc4cd51e3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (R r s : ℝ) (h₁ : 0 < R ∧ 0 < r ∧ 0 < s) (h₂ : R + r = s) : 4 * R ^ 2 + 4 * R * r + 3 * r ^ 2 ≥ s ^ 2 := by
  (intros; nlinarith [sq_nonneg (R), sq_nonneg (r), sq_nonneg (s), sq_nonneg (R - r), sq_nonneg (R - s), sq_nonneg (r - s), sq_nonneg (R + r), sq_nonneg (R + s), sq_nonneg (r + s)])
