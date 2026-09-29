-- Prove2me | solution 1 for lean_workbook_plus_30124
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:55:39.135997+00:00
-- url     : https://prove2.me/submissions/dd0065fc-078b-4707-9559-4886d5c6aa00

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (f : ℕ → ℝ) (h₀ : f 0 = a) (h₁ : f 1 = b) (h₂ : ∀ n, f (2 * n) = 2 * n + a) (h₃ : ∀ n, f (2 * n + 1) = 2 * n + b) : ∃ a b, f 0 = a ∧ f 1 = b ∧ (∀ n, f (2 * n) = 2 * n + a) ∧ (∀ n, f (2 * n + 1) = 2 * n + b) := by
  (intros; simp_all)
