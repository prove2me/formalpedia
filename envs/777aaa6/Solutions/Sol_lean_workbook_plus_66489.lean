-- Prove2me | solution 1 for lean_workbook_plus_66489
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:03.638464+00:00
-- url     : https://prove2.me/submissions/6ecdef3c-a838-461e-94a5-af7c8c45c47b

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 7) (a_rec : ∀ n, a (n + 2) = 2 * a (n + 1) + 15 * a n) : ∃ f : ℕ → ℕ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
