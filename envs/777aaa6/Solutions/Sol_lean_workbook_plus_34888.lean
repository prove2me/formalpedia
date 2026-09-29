-- Prove2me | solution 1 for lean_workbook_plus_34888
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:29.830591+00:00
-- url     : https://prove2.me/submissions/eac5b012-2a8a-42b5-9352-116a1a0943a2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 2) (a_rec : ∀ n, a (n + 2) = 4 * a (n + 1) + a n) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
