-- Prove2me | solution 2 for lean_workbook_plus_42472
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:17:18.512805+00:00
-- url     : https://prove2.me/submissions/0e52c9c7-441d-427e-a66b-9e7f0ada6be8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ)
  (h₀ : 0 < x)
  (h₁ : x < 2) :
  0 < x ∧ x < 2 := by
  (intros; simp_all)
