-- Prove2me | solution 1 for lean_workbook_plus_66836
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:14:42.827215+00:00
-- url     : https://prove2.me/submissions/b4bb8b14-e0af-4b94-9553-293042b6e7e6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a1 : a 0 = 1) (a2 : a 1 = 5) (a_rec : ∀ n, a (n + 1) = a n * a (n - 1) / Real.sqrt (a n ^ 2 + a (n - 1) ^ 2 + 1)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
