-- Prove2me | solution 1 for lean_workbook_plus_14217
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:30:29.990968+00:00
-- url     : https://prove2.me/submissions/a3ab1ede-d4b9-4df7-befe-86e801eb4fe0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (f : ℝ → ℝ) (hf: f = fun x => if x ≠ -Real.sqrt 3 ∧ x ≠ Real.sqrt 3 then a else 0) : ∀ x, x ≠ -Real.sqrt 3 ∧ x ≠ Real.sqrt 3 → f x = a := by
  (intros; simp_all)
