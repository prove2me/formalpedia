-- Prove2me | solution 1 for lean_workbook_plus_81764
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:36:14.077989+00:00
-- url     : https://prove2.me/submissions/b12049e5-5900-4f2d-8ea7-260b112f98d0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = a n / (1 + n * a n)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
