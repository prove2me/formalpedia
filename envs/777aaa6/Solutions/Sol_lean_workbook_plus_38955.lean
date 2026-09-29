-- Prove2me | solution 1 for lean_workbook_plus_38955
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:15.088588+00:00
-- url     : https://prove2.me/submissions/cf3051a0-7598-4818-a103-ccedd132cbee

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A : Set ℝ) (hA : A = {0}) : ∃ f : ℝ → ℝ, ∀ x, f x = 0 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
