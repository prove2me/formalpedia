-- Prove2me | solution 1 for lean_workbook_plus_40051
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:51.330928+00:00
-- url     : https://prove2.me/submissions/8c1870a5-2b8d-40b2-9b78-219b87a2a7d8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (U : ℕ → ℤ) (h₁ : U 1 = 1) (h₂ : U 2 = 1) (h₃ : ∀ k, U (2 * k + 1) = 3 * U (2 * k) + 6 * U (2 * k - 1)) (h₄ : ∀ k, U (2 * k + 2) = 3 * U (2 * k + 1) - 6 * U (2 * k)) : ∃ f : ℕ → ℤ, ∀ n, U n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
