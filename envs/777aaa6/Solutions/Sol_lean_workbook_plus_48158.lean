-- Prove2me | solution 1 for lean_workbook_plus_48158
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:50:14.964565+00:00
-- url     : https://prove2.me/submissions/361321b8-1789-41f3-bbe3-19e225bafae8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) : ∃ f : ℕ → ℝ, ∀ n, f n = 1 / (n + 1)^2 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
