-- Prove2me | solution 2 for lean_workbook_plus_58747
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:44:34.690947+00:00
-- url     : https://prove2.me/submissions/d152914e-ad56-440a-a58d-c23dff8b4390

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a1 : a 0 = 4) (a2 : a 1 = 7) (a_rec : ∀ n, n ≥ 2 → a (n + 1) = 2 * a n - a (n - 1) + 2) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
