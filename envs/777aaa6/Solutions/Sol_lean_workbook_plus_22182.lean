-- Prove2me | solution 1 for lean_workbook_plus_22182
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:03.167033+00:00
-- url     : https://prove2.me/submissions/c79cf4d7-b29d-41c2-ad11-75150121ffc4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (T : ℕ → ℝ) (h : T 1 = 1) (h2 : ∀ n, n > 1 → T n = 1 / (4 - T (n - 1))) : ∃ f : ℕ → ℝ, ∀ n, T n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
