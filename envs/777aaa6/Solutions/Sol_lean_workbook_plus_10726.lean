-- Prove2me | solution 1 for lean_workbook_plus_10726
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:41:06.052983+00:00
-- url     : https://prove2.me/submissions/2d0d33de-76ed-4f9b-ad89-128e3aa25eb6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : ℝ) : (p^2 + 1) * (q^2 + 1) ≥ (1 + p * q)^2 := by
  (intros; nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (p - q), sq_nonneg (p + q)])
