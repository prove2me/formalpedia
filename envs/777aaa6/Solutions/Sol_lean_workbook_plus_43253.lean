-- Prove2me | solution 1 for lean_workbook_plus_43253
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:36.772446+00:00
-- url     : https://prove2.me/submissions/ae854b89-00cf-48fe-bffc-7e1b7dd5f35c

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (D : ℕ → ℕ) (h : D 1 = 0 ∧ D 2 = 1 ∧ ∀ n, D (n + 1) = n * (D n + D (n - 1))) : ∃ f : ℕ → ℕ, ∀ n, D n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
