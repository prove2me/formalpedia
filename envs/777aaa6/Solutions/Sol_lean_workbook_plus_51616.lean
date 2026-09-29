-- Prove2me | solution 1 for lean_workbook_plus_51616
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:05:52.77842+00:00
-- url     : https://prove2.me/submissions/d74ec091-084d-4ca2-9dec-aa2ca8e4933f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = 1 / 2 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
