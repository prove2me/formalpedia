-- Prove2me | solution 1 for lean_workbook_plus_1852
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:32:38.160395+00:00
-- url     : https://prove2.me/submissions/330837bd-7e3d-46ec-aa09-22effd36c3f5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (f : ℝ → ℝ) (hf: f = fun x ↦ x^2 + a) : (∀ x, f x = x^2 + a) := by
  (intros; simp_all)
