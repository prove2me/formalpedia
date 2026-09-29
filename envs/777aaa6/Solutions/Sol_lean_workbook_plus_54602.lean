-- Prove2me | solution 1 for lean_workbook_plus_54602
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:18.068444+00:00
-- url     : https://prove2.me/submissions/0a30be04-c157-4ebd-b0be-c78093e433cb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℤ) (a0 : a 0 = 3) (a_rec : ∀ n, a (n + 1) = a n ^ 2 - 2) : ∃ f : ℕ → ℤ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
