-- Prove2me | solution 1 for lean_workbook_plus_33431
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:43.469855+00:00
-- url     : https://prove2.me/submissions/dd6a4316-2806-464b-a7e7-6a2343d390d1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun (x : ℝ) => ↑⌊x⌋) : ∀ x, f x = ⌊x⌋ := by
  (intros; simp_all)
