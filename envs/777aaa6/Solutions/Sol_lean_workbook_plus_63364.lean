-- Prove2me | solution 1 for lean_workbook_plus_63364
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:08.528006+00:00
-- url     : https://prove2.me/submissions/b945c50b-6544-4c75-a8c6-e8cbc35fa5d0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (u : ℕ → ℕ) (u1 : u 0 = 2) (u2 : u 1 = 8) (un : ∀ n, u (n + 2) = 4 * u (n + 1) - u n) : ∃ f : ℕ → ℕ, ∀ n, u n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
