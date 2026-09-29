-- Prove2me | solution 1 for lean_workbook_plus_28434
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:42:00.859867+00:00
-- url     : https://prove2.me/submissions/baf4fece-4dcd-45a0-be88-cfa1c33933e7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℕ) (a1 : a 0 = 3) (a_rec : ∀ n, a (n + 1) = a n + 5 + 4 * 2 ^ n + 3 ^ (n + 1) + 2 * 4 ^ n + 5 ^ n) : ∃ f : ℕ → ℕ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
