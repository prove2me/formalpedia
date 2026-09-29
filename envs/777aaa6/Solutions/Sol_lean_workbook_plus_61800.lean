-- Prove2me | solution 1 for lean_workbook_plus_61800
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:19:38.505373+00:00
-- url     : https://prove2.me/submissions/c02d2c83-547a-4080-b4de-0efc68aa12b3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: ∀ x y: ℝ, x > y → f x > f y) : ∀ x y: ℝ, x > y → f x > f y := by
  (intros; simp_all)
