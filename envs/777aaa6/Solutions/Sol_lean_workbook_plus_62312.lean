-- Prove2me | solution 1 for lean_workbook_plus_62312
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:47.620197+00:00
-- url     : https://prove2.me/submissions/e9237677-68dc-4725-ba17-70cf2a604460

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : x ≥ x^2 := by
  (intros; nlinarith [sq_nonneg (x)])
