-- Prove2me | solution 1 for lean_workbook_plus_67856
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:13:31.301535+00:00
-- url     : https://prove2.me/submissions/bd14def5-fdd2-4a47-97ab-f0a11cf523a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = -2 * x := by
  (intros; exact ⟨_, fun _ => rfl⟩)
