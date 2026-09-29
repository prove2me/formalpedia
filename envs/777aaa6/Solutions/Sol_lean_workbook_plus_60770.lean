-- Prove2me | solution 1 for lean_workbook_plus_60770
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:03:02.075143+00:00
-- url     : https://prove2.me/submissions/2e9e8472-a2c9-4a16-8b4c-340c3e4e6791

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ f : ℚ → ℚ, ∀ x, f x = if x > √2 then 1 else 0 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
