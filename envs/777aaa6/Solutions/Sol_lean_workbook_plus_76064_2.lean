-- Prove2me | solution 2 for lean_workbook_plus_76064
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:50.436682+00:00
-- url     : https://prove2.me/submissions/6153653c-87e1-4327-ad89-8c02faeb8e47

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℕ) (a0 : a 0 = 0) (a1 : a 1 = 2) (a_rec : ∀ n, n ≥ 2 → a n + a (n - 2) = 2 * (a (n - 1) + 1)) : ∃ f : ℕ → ℕ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
