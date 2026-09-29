-- Prove2me | solution 1 for lean_workbook_plus_38012
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:52:59.666767+00:00
-- url     : https://prove2.me/submissions/0eb059eb-3f55-4d0c-94f6-f13a5befa5ad

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : 0 ≤ x)
  (h₁ : 0 ≤ y) :
  Real.sqrt x ^ 2 = x ∧ Real.sqrt y ^ 2 = y := by
  (intros; simp_all)
