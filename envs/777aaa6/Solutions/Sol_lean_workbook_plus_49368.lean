-- Prove2me | solution 1 for lean_workbook_plus_49368
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:29.692083+00:00
-- url     : https://prove2.me/submissions/d9963e31-1920-4e64-840c-249c512e58ce

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℕ) (a0 : a 0 = 1) (a1 : a 1 = 6) (a_rec : ∀ n, a (n + 2) = 6 * a (n + 1) - a n) : ∃ f : ℕ → ℕ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
