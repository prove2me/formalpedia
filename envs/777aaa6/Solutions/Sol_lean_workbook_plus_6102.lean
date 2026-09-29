-- Prove2me | solution 1 for lean_workbook_plus_6102
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:58:26.048595+00:00
-- url     : https://prove2.me/submissions/aec0bccd-a5e6-4ad0-a593-bbf5227523c8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ f : ℝ → ℝ, ∀ a M : ℝ, (∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo a δ → |f x - M| < ε) ↔ ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, x ∈ Set.Ioo a δ → |f x - M| < ε := by
  norm_num
