-- Prove2me | solution 1 for lean_workbook_plus_64389
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:40.68207+00:00
-- url     : https://prove2.me/submissions/382e6cdc-0acc-4b38-ba71-bbcb08773534

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f 0 = 0) (hf2: ∀ x, f (f x) = 2 * f x) : ∃ g : ℝ → ℝ, ∀ x, g x = f x := by
  (intros; exact ⟨_, fun _ => rfl⟩)
