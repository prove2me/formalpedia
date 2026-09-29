-- Prove2me | solution 1 for lean_workbook_plus_79552
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:38.27163+00:00
-- url     : https://prove2.me/submissions/0198399c-807e-4e3c-b67b-69eff0a9a6c7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℚ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = (1 + 4 * a n + Real.sqrt (1 + 24 * a n)) / 16) : ∃ f : ℕ → ℚ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
