-- Prove2me | solution 1 for lean_workbook_plus_53850
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:46.989668+00:00
-- url     : https://prove2.me/submissions/6d15539f-6b04-4de4-956a-bbefef17f077

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (g : ℂ → ℂ) (hg : g = fun z => -2 * z ^ 5 + 6 * z ^ 3 - z + 1) : ∃ n, n = {z : ℂ | g z = 0 ∧ ‖z‖ < 1} := by
  norm_num
