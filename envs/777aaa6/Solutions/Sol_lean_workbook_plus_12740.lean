-- Prove2me | solution 1 for lean_workbook_plus_12740
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:32:11.451485+00:00
-- url     : https://prove2.me/submissions/b29c4066-5cc3-48cb-96db-bf5735d4b2a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : (a^2+b^2)*(a^2+c^2) ≥ 4*a^2*b*c := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b), sq_nonneg (a + c), sq_nonneg (b + c)])
