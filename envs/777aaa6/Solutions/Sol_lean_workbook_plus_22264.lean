-- Prove2me | solution 1 for lean_workbook_plus_22264
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:12:11.168993+00:00
-- url     : https://prove2.me/submissions/3b673482-b974-46a7-9cff-67a0e166b80f

import Mathlib
set_option autoImplicit false
theorem solution : ∃ f : ℝ → ℝ, ∀ x > 0, f x = x := by
  exact ⟨id, fun _ _ => rfl⟩
