-- Prove2me | solution 1 for lean_workbook_plus_73121
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:50:38.179976+00:00
-- url     : https://prove2.me/submissions/154bd78e-19d1-423d-9c40-d5a4e78a945a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^2 + a * b + b^2 ≤ 3 / 2 * (a^2 + b^2) := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
