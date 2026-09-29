-- Prove2me | solution 1 for lean_workbook_plus_24368
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:42:08.050182+00:00
-- url     : https://prove2.me/submissions/8c4166ab-3859-4018-8211-334cae84f67d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℕ) (a0 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = 5 * a n * (5 * (a n)^4 - 5 * (a n)^2 + 1)) : ∃ f : ℕ → ℕ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
