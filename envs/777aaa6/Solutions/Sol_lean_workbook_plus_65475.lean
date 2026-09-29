-- Prove2me | solution 1 for lean_workbook_plus_65475
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:12.431989+00:00
-- url     : https://prove2.me/submissions/363081f6-4efe-402d-978a-0a9bcaf7e302

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {b c : ℝ} (hbc : b * c ≤ 1) :
  (Real.sqrt (2 / (1 + b * c)) - 1)^2 ≥ 0 := by
  (intros; positivity)
