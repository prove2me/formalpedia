-- Prove2me | solution 1 for lean_workbook_plus_65416
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:06:35.116899+00:00
-- url     : https://prove2.me/submissions/4a7290da-cc66-40e3-a5a3-4b2b300bc540

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun (x:ℝ) => x) : ∀ x, f x = x := by
  (intros; simp_all)
