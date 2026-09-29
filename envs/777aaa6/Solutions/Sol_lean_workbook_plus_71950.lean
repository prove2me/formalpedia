-- Prove2me | solution 1 for lean_workbook_plus_71950
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:56.159901+00:00
-- url     : https://prove2.me/submissions/659be419-df0a-4779-b496-5ff981c9fd5d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = 1 / Real.sqrt 3 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
