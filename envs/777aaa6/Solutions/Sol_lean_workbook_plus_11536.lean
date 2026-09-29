-- Prove2me | solution 1 for lean_workbook_plus_11536
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:48:27.081286+00:00
-- url     : https://prove2.me/submissions/21fa2240-743d-445b-9549-ab18e9a3d054

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x => 0) : ∀ x, f x = 0 := by
  (intros; simp_all)
