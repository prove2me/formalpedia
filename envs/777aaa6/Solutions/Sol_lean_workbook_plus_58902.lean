-- Prove2me | solution 1 for lean_workbook_plus_58902
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:13.177585+00:00
-- url     : https://prove2.me/submissions/20d0c482-cc2d-4baa-8e26-ce4ccd830476

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (P : ℝ → ℝ → ℝ → Prop) (h : ∀ x y z : ℝ, P x y z) : P x y z := by
  (intros; simp_all)
