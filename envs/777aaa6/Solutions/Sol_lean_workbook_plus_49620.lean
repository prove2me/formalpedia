-- Prove2me | solution 1 for lean_workbook_plus_49620
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:35:57.087247+00:00
-- url     : https://prove2.me/submissions/0ef3bed5-2e8c-4bfd-9cb2-b2fba2442d24

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u : ℝ) (hu : u ∈ ({0, 1 / 2} : Finset ℝ)) : u = 0 ∨ u = 1 / 2 := by
  (intros; simp_all)
