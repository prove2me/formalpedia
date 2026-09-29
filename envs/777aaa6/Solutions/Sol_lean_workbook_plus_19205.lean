-- Prove2me | solution 1 for lean_workbook_plus_19205
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:45.315028+00:00
-- url     : https://prove2.me/submissions/9ea14b6b-f28e-4168-ad74-534e5495354a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℤ) (h₁ : a + b = 56) (h₂ : a - b = 30) : a^2 + b^2 = 2018 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
