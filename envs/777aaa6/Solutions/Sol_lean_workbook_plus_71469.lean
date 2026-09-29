-- Prove2me | solution 1 for lean_workbook_plus_71469
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:56.37019+00:00
-- url     : https://prove2.me/submissions/df848e8d-9dd4-4d0e-a7ed-296bc183e172

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ f : ℚ → ℚ, ∀ x, f x = x + 1 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
