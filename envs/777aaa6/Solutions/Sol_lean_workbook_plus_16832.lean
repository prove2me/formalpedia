-- Prove2me | solution 1 for lean_workbook_plus_16832
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:22:09.396324+00:00
-- url     : https://prove2.me/submissions/af3c11d5-0837-406c-a9d6-b4ed85c84a16

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (A : Set ℝ) (hA : A = {0}) : ∃ f : ℝ → ℝ, ∀ x, f x = 0 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
