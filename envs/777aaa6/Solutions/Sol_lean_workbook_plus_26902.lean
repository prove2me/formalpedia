-- Prove2me | solution 1 for lean_workbook_plus_26902
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:15:16.529457+00:00
-- url     : https://prove2.me/submissions/6ff3759d-656b-4407-8de9-3f78ea33658b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (C : ℝ) (h : ∀ x, (x ≠ 0 → f x = 0 ∨ f x = 1) ∧ f 0 = C) : ∃ C, ∀ x, (x ≠ 0 → f x = 0 ∨ f x = 1) ∧ f 0 = C := by
  (intros; simp_all)
