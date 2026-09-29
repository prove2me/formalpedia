-- Prove2me | solution 1 for lean_workbook_plus_60260
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:33:22.243104+00:00
-- url     : https://prove2.me/submissions/4c3ddd83-8649-4d1f-ab1b-a1839aec4462

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (hab : a + b = 2) : a ^ 4 + b ^ 4 ≥ (a + b) * (a ^ 3 + b ^ 3) / 2 := by
  (intros; nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (a - b), sq_nonneg (a + b)])
