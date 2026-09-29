-- Prove2me | solution 1 for lean_workbook_plus_25398
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:42:12.812481+00:00
-- url     : https://prove2.me/submissions/0a434a9a-96d2-4a9f-aa56-0fb84d2e2621

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (μ : ℕ → ℕ) (h₀ : μ 0 = 2) (h₁ : μ 1 = 4) (h₂ : ∀ n ≥ 2, μ n = 4 * μ (n - 1) + μ (n - 2)) : ∃ f : ℕ → ℕ, ∀ n, μ n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
