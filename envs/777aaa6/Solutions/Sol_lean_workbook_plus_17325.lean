-- Prove2me | solution 1 for lean_workbook_plus_17325
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:06:07.040075+00:00
-- url     : https://prove2.me/submissions/2b5f680d-fdbf-4320-9702-0b50b8360265

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a c : ℝ) (h₁ : a ≠ 0) (h₂ : a * c = 0) : c = 0 := by
  (intros; simp_all)
