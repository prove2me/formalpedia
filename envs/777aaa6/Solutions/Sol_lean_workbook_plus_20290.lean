-- Prove2me | solution 1 for lean_workbook_plus_20290
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:05:26.840303+00:00
-- url     : https://prove2.me/submissions/4f6ea28c-d743-420e-81ef-b88eb37790dc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x₁ : ℝ) (y z : ℝ → ℝ) (h₁ : ∀ x, x ≤ x₁ → y x ≤ z x) : ∀ x, x ≤ x₁ → y x ≤ z x := by
  (intros; simp_all)
