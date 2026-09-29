-- Prove2me | solution 1 for lean_workbook_plus_40961
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:48.985896+00:00
-- url     : https://prove2.me/submissions/7336db93-8b07-4b21-aa88-288f79e0f9b0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℤ) (a0 : a 0 = 5) (a1 : a 1 = 35) (a_rec : ∀ n, a (n + 2) = 8 * a (n + 1) - a n) : ∃ f : ℕ → ℤ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
