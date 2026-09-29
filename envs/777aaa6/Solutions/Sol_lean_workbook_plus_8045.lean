-- Prove2me | solution 1 for lean_workbook_plus_8045
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:59:30.412907+00:00
-- url     : https://prove2.me/submissions/bb8cbf23-df04-47c1-8bf5-5dca9fa3c540

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q r s : ℝ)
  (h₀ : p = 2 / 5)
  (h₁ : q = 1 / 2)
  (h₂ : r = 3 / 5)
  (h₃ : s = 1 / 3)
  (h₄ : p * q = r * s) :
  p * q / (p * q + r * s) = 1 / 2 := by
  (intros; field_simp; nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (r), sq_nonneg (s), sq_nonneg (p - q), sq_nonneg (p - r), sq_nonneg (p - s), sq_nonneg (q - r), sq_nonneg (q - s), sq_nonneg (r - s), sq_nonneg (p + q), sq_nonneg (p + r), sq_nonneg (p + s), sq_nonneg (q + r), sq_nonneg (q + s), sq_nonneg (r + s)])
