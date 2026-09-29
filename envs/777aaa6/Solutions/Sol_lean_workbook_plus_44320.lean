-- Prove2me | solution 1 for lean_workbook_plus_44320
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:28:02.61665+00:00
-- url     : https://prove2.me/submissions/1a393142-76f7-4485-923e-a82b3c4ed604

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℕ → ℝ) (n : ℕ) (hx: x 1 = 1) (hn: ∀ n, (x n)^2 + 1 = (n + 1) * (x (n + 1))^2) : ∃ f : ℕ → ℝ, ∀ n, x n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
