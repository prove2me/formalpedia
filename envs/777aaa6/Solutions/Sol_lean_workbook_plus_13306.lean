-- Prove2me | solution 1 for lean_workbook_plus_13306
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:36.340734+00:00
-- url     : https://prove2.me/submissions/193dcddc-b746-44ad-8a7b-d9451c1db844

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p : ℝ)
  (h₀ : 0 ≤ p ∧ p ≤ 1) :
  (1 - p) * (1 - p) = (1 - p)^2 := by
  (intros; linarith)
