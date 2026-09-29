-- Prove2me | solution 1 for lean_workbook_plus_34026
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:15:56.285862+00:00
-- url     : https://prove2.me/submissions/1dc08479-eda6-47b1-92c2-ce2329b931e7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ)
  (h₀ : b = a + 1) :
  b^2 - a^2 = a + b := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
