-- Prove2me | solution 2 for lean_workbook_plus_51878
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:34.330296+00:00
-- url     : https://prove2.me/submissions/7599563c-e37d-4d86-99ca-277492d306da

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 2) (a_rec : ∀ n, n > 1 → a n = 4 * a (n - 1) - 5 * a (n - 2)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
