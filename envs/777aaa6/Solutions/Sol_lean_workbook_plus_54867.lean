-- Prove2me | solution 1 for lean_workbook_plus_54867
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:01:52.428995+00:00
-- url     : https://prove2.me/submissions/7185535d-fc81-4cd8-95d6-d6c6943993f1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (B : ℝ) (hB : 2.25 < B ∧ B ≤ 3) :
  (27 - B) * (12 * B - 27) ≥ 9 * (4 * B ^ 2 + 11 * B - 45) := by
  (intros; nlinarith [sq_nonneg (B)])
