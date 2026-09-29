-- Prove2me | solution 1 for lean_workbook_plus_78696
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:45.874139+00:00
-- url     : https://prove2.me/submissions/517edf8f-30fa-4f8b-bd0a-5df9eaaeaa40

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (U : ℕ → ℕ) (h : U 1 = 1 ∧ ∀ n, U (n + 1) = U n + 3 * n ^ 2 + 5 * n ^ 4) : ∃ f : ℕ → ℕ, ∀ n, U n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
