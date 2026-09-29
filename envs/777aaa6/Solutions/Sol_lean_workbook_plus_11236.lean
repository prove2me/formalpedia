-- Prove2me | solution 1 for lean_workbook_plus_11236
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:47:53.148215+00:00
-- url     : https://prove2.me/submissions/167e060f-a2e3-4fb6-aba4-cc70b3a3d9a1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (R C : ℝ → ℝ) (P : ℝ → ℝ) (h₁ : P = R - C) : P x = R x - C x := by
  (intros; simp_all)
