-- Prove2me | solution 1 for lean_workbook_plus_11280
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:19.64143+00:00
-- url     : https://prove2.me/submissions/e7ed36a2-ec7c-49c9-bbb0-8558f3aa6a82

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a_n : ∀ n, a n = 0.25 * ((Real.sqrt 2 + 1) ^ (2 * n - 1) - (Real.sqrt 2 - 1) ^ (2 * n - 1) + 2)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
