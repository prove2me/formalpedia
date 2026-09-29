-- Prove2me | solution 1 for lean_workbook_plus_25369
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:39.123891+00:00
-- url     : https://prove2.me/submissions/07073d4f-7415-4a1d-8241-7def00c054d8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a^2 + b = 3) (h₂ : 4*a^2*b = 5) : a^2 + b = 3 ∧ 4*a^2*b = 5 := by
  (intros; simp_all)
