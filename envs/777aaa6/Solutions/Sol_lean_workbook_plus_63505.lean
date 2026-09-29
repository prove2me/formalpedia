-- Prove2me | solution 1 for lean_workbook_plus_63505
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:08:13.412278+00:00
-- url     : https://prove2.me/submissions/23a8f2a7-ae79-47d7-8599-030249303f7b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (n : ℕ) (T : ℕ → ℝ) (h₀ : T 0 = a) (h₁ : T 1 = b) (h₂ : ∀ n ≥ 2, T n = (1 + T (n - 1)) / T (n - 2)) : ∃ f : ℕ → ℝ, ∀ n, T n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
