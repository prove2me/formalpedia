-- Prove2me | solution 1 for lean_workbook_plus_66119
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:31:45.20877+00:00
-- url     : https://prove2.me/submissions/fb959e5e-fc1a-4a8e-9a31-9d78292ccdf5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (T : ℕ → ℝ) (h₁ : T 1 = 1) (h₂ : ∀ n, n > 1 → T n = 1 / (4 - T (n - 1))) : ∃ f : ℕ → ℝ, ∀ n, T n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
