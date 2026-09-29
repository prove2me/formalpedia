-- Prove2me | solution 1 for lean_workbook_plus_34047
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:00.998296+00:00
-- url     : https://prove2.me/submissions/0e3ad8e0-7144-4a60-8bf7-29c7862e1050

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ f : ℝ → ℝ, ∀ x, f x = 2 * x - 1 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
