-- Prove2me | solution 1 for lean_workbook_plus_17206
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:35.138962+00:00
-- url     : https://prove2.me/submissions/b7de579a-8584-4ec0-96db-3b4fde9ed023

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : ℤ)
  (h₀ : p - q = 2)
  (h₁ : p^3 - q^3 = 31106) :
  p * q = 5183 := by
  (intros; nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (p - q), sq_nonneg (p + q)])
