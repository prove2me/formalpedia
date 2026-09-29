-- Prove2me | solution 1 for lean_workbook_plus_25427
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:35:57.765923+00:00
-- url     : https://prove2.me/submissions/cb149f18-e07d-42b0-9670-27f02a578139

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : (x + 6)^2 = 0) :
  x = -6 := by
  (intros; nlinarith [sq_nonneg (x)])
