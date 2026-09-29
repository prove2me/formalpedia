-- Prove2me | solution 1 for lean_workbook_plus_54034
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:29.533689+00:00
-- url     : https://prove2.me/submissions/550a0db4-8ca0-49de-b027-5b5bea4b9213

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf : ∀ x, f x = -x) : ∀ x, f x = -x := by
  (intros; simp_all)
