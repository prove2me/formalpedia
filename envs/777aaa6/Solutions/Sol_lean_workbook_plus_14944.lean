-- Prove2me | solution 1 for lean_workbook_plus_14944
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:18.608649+00:00
-- url     : https://prove2.me/submissions/79bfc3f2-ca23-4988-b2ac-5713680b805d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (t : ℝ) (ht: t >= 1): 3 * t + 1 / t ≥ 4 := by
  (intros; field_simp; nlinarith [sq_nonneg (t)])
