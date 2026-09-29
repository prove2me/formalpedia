-- Prove2me | solution 1 for lean_workbook_plus_34572
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:16:56.324129+00:00
-- url     : https://prove2.me/submissions/fbc40b1c-7cd9-4f26-8c29-a6bfa8b88a87

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x) : ∃ f : ℝ → ℝ, ∀ x, f x = if x ≥ 0 then 0 else g x := by
  (intros; exact ⟨_, fun _ => rfl⟩)
