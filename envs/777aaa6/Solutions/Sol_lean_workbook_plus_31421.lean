-- Prove2me | solution 1 for lean_workbook_plus_31421
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:03.389379+00:00
-- url     : https://prove2.me/submissions/ba323685-926c-4815-a1ae-6fdbbd8f0da3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (m n u : ℤ) (h₁ : m = 2 * u) (h₂ : m^2 - 2 * m = 12 * n^2) : u * (u - 1) = 3 * n^2 := by
  (intros; nlinarith [sq_nonneg (m), sq_nonneg (n), sq_nonneg (u), sq_nonneg (m - n), sq_nonneg (m - u), sq_nonneg (n - u), sq_nonneg (m + n), sq_nonneg (m + u), sq_nonneg (n + u)])
