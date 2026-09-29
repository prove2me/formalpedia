-- Prove2me | solution 1 for lean_workbook_plus_44446
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:15.347418+00:00
-- url     : https://prove2.me/submissions/d04696cd-70ea-4366-9514-54acb2373f4d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (A : Set ℝ) (hA : A = Set.Icc 0 1) :
  ContinuousOn f A ↔ ∀ x ∈ A, ContinuousWithinAt f A x := by
  rfl
