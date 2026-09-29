-- Prove2me | solution 1 for lean_workbook_plus_51082
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:17.640393+00:00
-- url     : https://prove2.me/submissions/2b3625b9-6171-40b6-a049-b4672992ea17

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx1 : -3 ≤ x) (hx2 : x ≤ -1/3) : x / (x^2 + 1) ≤ -3/10 := by
  (intros; field_simp; nlinarith [sq_nonneg (x)])
