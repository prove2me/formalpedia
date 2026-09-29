-- Prove2me | solution 1 for lean_workbook_plus_77530
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:24.11695+00:00
-- url     : https://prove2.me/submissions/9b535f8b-23de-4657-b172-88ed672016ee

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a1 : a 1 = 1) (a2 : a 2 = 2) (a_rec : ∀ n, a (n + 1) * a (n - 1) = a n ^ 2 + 5) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
