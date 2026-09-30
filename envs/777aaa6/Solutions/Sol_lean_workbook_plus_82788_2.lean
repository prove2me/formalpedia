-- Prove2me | solution 2 for lean_workbook_plus_82788
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:32.832677+00:00
-- url     : https://prove2.me/submissions/dc0dbb69-9d39-4c76-b29e-c343683a6bc4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℤ) (a0 : a 0 = 2) (a_rec : ∀ n, a (n + 1) + 3 * a n = n ^ 3 - 1) : ∃ f : ℕ → ℤ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
