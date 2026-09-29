-- Prove2me | solution 1 for lean_workbook_plus_6680
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:49:33.788042+00:00
-- url     : https://prove2.me/submissions/a4014fdb-2131-4d81-9a16-fb411897cee1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (g : ℝ → ℝ) (h : ∀ x, g (g (g x)) = x^2 + 3*x + 4) : ∃ v, g (g 2) = v := by
  norm_num
