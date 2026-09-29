-- Prove2me | solution 1 for lean_workbook_plus_37031
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:54:12.255743+00:00
-- url     : https://prove2.me/submissions/a8bd72a7-d6f0-4177-9c50-898b6bf71684

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e : ℝ) : (b - a/2)^2 + (c - a/2)^2 + (d - a/2)^2 + (e - a/2)^2 ≥ 0 := by
  (intros; positivity)
