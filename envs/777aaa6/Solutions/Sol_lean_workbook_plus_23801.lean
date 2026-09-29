-- Prove2me | solution 1 for lean_workbook_plus_23801
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:42:10.43648+00:00
-- url     : https://prove2.me/submissions/54d176ea-84cb-4ad3-947c-11c5a5559701

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n : ℕ) (a : ℕ → ℕ) (a0 : a 0 = 1) (a1 : a 1 = 3) (a_rec : ∀ n ≥ 1, a (n + 2) = 2 * a (n + 1) + 2 * a n - 3) : ∃ f : ℕ → ℕ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
