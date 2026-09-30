-- Prove2me | solution 2 for lean_workbook_plus_13642
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:23:06.032771+00:00
-- url     : https://prove2.me/submissions/53062326-d2e6-44b7-8e42-c3d2649b4d15

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun (t : ℝ) => t - 1/2) : ∀ t ∈ Set.Ico (0 : ℝ) 1, f t = t - 1/2 := by
  (intros; simp_all)
