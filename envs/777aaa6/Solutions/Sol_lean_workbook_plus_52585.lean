-- Prove2me | solution 1 for lean_workbook_plus_52585
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:22.915184+00:00
-- url     : https://prove2.me/submissions/53186b47-5b4b-4e90-8624-93aa966f6ee7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a m n : ℝ)
  (h₀ : n^2 + a^2 = 25)
  (h₁ : m^2 + a^2 = 9)
  (h₂ : m + n = 7) :
  n - m = 16 / 7 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (m), sq_nonneg (n), sq_nonneg (a - m), sq_nonneg (a - n), sq_nonneg (m - n), sq_nonneg (a + m), sq_nonneg (a + n), sq_nonneg (m + n)])
