-- Prove2me | solution 1 for lean_workbook_plus_72995
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:50:43.848328+00:00
-- url     : https://prove2.me/submissions/11e44433-72d9-42b8-b0b8-1898f7c77ad7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a1 : ℝ) (h1 : a1 = a 0) (h2 : ∀ n, a (n + 1) = 1 / (4 - 3 * a n)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
