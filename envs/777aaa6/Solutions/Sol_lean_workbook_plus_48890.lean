-- Prove2me | solution 1 for lean_workbook_plus_48890
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:37:30.726737+00:00
-- url     : https://prove2.me/submissions/9cd15107-fe65-4f3d-8162-c35212d2c30a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (hx : x 1 = √3 / 6) (hn : ∀ n, x (n + 1) = 24 * x n ^ 3 - 12 * Real.sqrt 6 * x n ^ 2 + 15 * x n - Real.sqrt 6) : ∃ f : ℕ → ℝ, ∀ n, x n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
