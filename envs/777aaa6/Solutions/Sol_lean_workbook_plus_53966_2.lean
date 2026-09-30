-- Prove2me | solution 2 for lean_workbook_plus_53966
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:32.037598+00:00
-- url     : https://prove2.me/submissions/ce1afafb-39ff-493c-b0a0-541d300dab4e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a0 : a 0 = 1) (a1 : a 1 = 3) (a_rec : ∀ n, a (n + 2) = 2 * a (n + 1) + a n) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
