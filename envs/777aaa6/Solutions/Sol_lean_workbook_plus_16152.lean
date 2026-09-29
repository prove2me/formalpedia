-- Prove2me | solution 1 for lean_workbook_plus_16152
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:49:19.000206+00:00
-- url     : https://prove2.me/submissions/be7e9225-f8ab-450a-9f3e-50334eb5c417

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∃ f : ℤ → ℤ, ∀ x, f x = -x - 1 := by
  (intros; exact ⟨_, fun _ => rfl⟩)
