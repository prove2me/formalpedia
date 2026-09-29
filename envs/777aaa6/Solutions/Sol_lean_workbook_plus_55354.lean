-- Prove2me | solution 1 for lean_workbook_plus_55354
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:20.308333+00:00
-- url     : https://prove2.me/submissions/3409af26-b954-4c0d-8c0c-ca660847d95d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℚ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = (a n ^ 2 + 3) / (a n + 1)) : ∃ f : ℕ → ℚ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
