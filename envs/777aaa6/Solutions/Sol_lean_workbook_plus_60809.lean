-- Prove2me | solution 1 for lean_workbook_plus_60809
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:32:50.733931+00:00
-- url     : https://prove2.me/submissions/0e281730-e6ad-4298-98d3-1af41cb20c3e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : a + 2 * b + c = -1 → c = -1 - a - 2 * b := by
  (intros; linarith)
