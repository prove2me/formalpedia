-- Prove2me | solution 1 for lean_workbook_plus_34115
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:53.667708+00:00
-- url     : https://prove2.me/submissions/2d68c291-b28a-43a9-b1a3-9d1f54f7803a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n:ℕ) (u : ℕ → ℕ) (h₁ : u 0 = 6) (h₂ : u 1 = 42) (h₃ : ∀ n, u (n + 2) = u (n + 1) + 6 * u n + 6 * n) : ∃ f:ℕ → ℕ, ∀ n, u n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
