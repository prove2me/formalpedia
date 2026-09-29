-- Prove2me | solution 1 for lean_workbook_plus_77352
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:02:00.409035+00:00
-- url     : https://prove2.me/submissions/b0e70cea-c946-4343-b862-a988b96beef4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (A : Set ℝ) (hA : A = {0}) (r a : ℝ → ℝ) (hr : r x = x) (ha : a x = 0) : ∃ F : ℝ → ℝ, ∀ x, F x = x := by
  (intros; exact ⟨_, fun _ => rfl⟩)
