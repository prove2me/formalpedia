-- Prove2me | solution 1 for lean_workbook_plus_53086
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:46:59.464695+00:00
-- url     : https://prove2.me/submissions/d3b9c1ae-b4aa-4c6e-842c-9735b6d29a95

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (f_def : ∀ x, f x = Real.sqrt x) : ∀ x, x ≥ 0 → f x ∈ Set.univ := by
  norm_num
