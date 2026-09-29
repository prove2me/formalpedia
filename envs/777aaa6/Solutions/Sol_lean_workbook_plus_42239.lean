-- Prove2me | solution 1 for lean_workbook_plus_42239
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:39.23204+00:00
-- url     : https://prove2.me/submissions/422694ac-f304-4600-af86-68acd2a05a67

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℕ) (a1 : a 0 = 1) (a2 : a 1 = 2) (a3 : a 2 = 2) (a_rec : ∀ n, a (n + 3) = a (n + 2) + a (n + 1) - 2 * a n) : ∃ f : ℕ → ℕ, ∀ k, a k = f k := by
  (intros; exact ⟨_, fun _ => rfl⟩)
