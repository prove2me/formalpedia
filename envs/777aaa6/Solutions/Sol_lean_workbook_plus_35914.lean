-- Prove2me | solution 1 for lean_workbook_plus_35914
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:23:08.572489+00:00
-- url     : https://prove2.me/submissions/40d0416b-fabd-4758-a85f-8812e16522ba

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) : x - 5 * (4:ℝ)^(1/3) = 0 ↔ x = 5 * (4:ℝ)^(1/3) := by
  exact sub_eq_zero
