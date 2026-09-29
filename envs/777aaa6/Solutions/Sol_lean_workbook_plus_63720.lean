-- Prove2me | solution 1 for lean_workbook_plus_63720
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:07:44.023613+00:00
-- url     : https://prove2.me/submissions/8219032a-c137-470a-9e39-ff1f882de3a1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u : ℝ) (h₁ : u + 1 = 2 * u^2) (h₂ : u > 0) : u = 1 := by
  (intros; nlinarith [sq_nonneg (u)])
