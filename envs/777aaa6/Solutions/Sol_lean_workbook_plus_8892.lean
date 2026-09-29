-- Prove2me | solution 1 for lean_workbook_plus_8892
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:33.630377+00:00
-- url     : https://prove2.me/submissions/7c4dd193-f24d-4f17-b886-62d124669a1a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (β : ℝ) (h : ∀ x, f x ≥ β) : ∀ x, f x ≥ β := by
  (intros; simp_all)
