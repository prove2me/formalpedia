-- Prove2me | solution 1 for lean_workbook_plus_78094
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:50.932731+00:00
-- url     : https://prove2.me/submissions/d810d1c2-cc78-4341-9b5f-3a659c5d39da

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (hx : x 1 = 0) (hx_rec : ∀ n, x (n + 1) = 5 * x n + Real.sqrt (24 * (x n)^2 + 1)) : ∃ f : ℕ → ℝ, ∀ n, x n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
