-- Prove2me | solution 1 for lean_workbook_plus_65553
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:49:22.596288+00:00
-- url     : https://prove2.me/submissions/1020062c-9e9a-46ac-8324-b68275ce62da

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℕ → ℝ) (a_n : ∀ n, a n = (Real.sqrt 2 / 2) * ((3 + 2 * Real.sqrt 2)^n - (3 - 2 * Real.sqrt 2)^n)) : ∃ f : ℕ → ℝ, ∀ n, a n = f n := by
  (intros; exact ⟨_, fun _ => rfl⟩)
