-- Prove2me | solution 1 for lean_workbook_plus_56657
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:22:37.682292+00:00
-- url     : https://prove2.me/submissions/714c9f5c-eeaf-4acb-861a-0446298dfe52

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a - b = 1) : a^3 - b^3 ≥ 1/4 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
