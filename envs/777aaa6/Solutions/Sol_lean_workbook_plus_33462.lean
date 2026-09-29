-- Prove2me | solution 1 for lean_workbook_plus_33462
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:06:46.363465+00:00
-- url     : https://prove2.me/submissions/93026fec-81a6-4de6-b9a0-4cd44c668bc4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (h₁ : x = Real.sqrt (28/3) * y) (h₂ : 0 ≤ y) (h₃ : y < 1) : x = Real.sqrt (28/3) * y ∧ 0 ≤ y ∧ y < 1 := by
  (intros; simp_all)
