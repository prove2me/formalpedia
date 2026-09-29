-- Prove2me | solution 1 for lean_workbook_plus_40129
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:40:51.206487+00:00
-- url     : https://prove2.me/submissions/33824cae-8410-4b94-a55f-2c904d11af40

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (z : ℝ) (h : z ≥ 2) : z / (z^2 + 1) ≤ 2/5 := by
  (intros; field_simp; nlinarith [sq_nonneg (z)])
