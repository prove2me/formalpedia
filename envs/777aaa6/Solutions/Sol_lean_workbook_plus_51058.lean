-- Prove2me | solution 1 for lean_workbook_plus_51058
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:19:19.996969+00:00
-- url     : https://prove2.me/submissions/38b3061f-fd1e-4c36-be33-de374c5529f3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (U : Set ℝ) (hU : U = {0}) : ∃ f : ℝ → ℝ, ∀ x, f x = 0 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
