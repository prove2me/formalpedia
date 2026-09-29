-- Prove2me | solution 1 for lean_workbook_plus_63441
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:08:21.129579+00:00
-- url     : https://prove2.me/submissions/2691fb05-9e6a-40b9-bf3f-e04eb4b69ca3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : y ≥ (3*x - 6) / 5 ↔ y ≥ 3*x/5 - 6/5 := by
  (intros; ring)
