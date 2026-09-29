-- Prove2me | solution 1 for lean_workbook_plus_43597
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:46.722474+00:00
-- url     : https://prove2.me/submissions/9eacda6c-4000-427a-adcf-f6cfde1523c1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℤ) (a1 : a 0 = 1) (a2 : a 1 = 3) (a_rec : ∀ n, a (n + 2) = a (n + 1) - 2 * a n - 1) : ∃ f : ℕ → ℤ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
