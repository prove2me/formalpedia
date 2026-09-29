-- Prove2me | solution 1 for lean_workbook_plus_42515
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:17:10.796854+00:00
-- url     : https://prove2.me/submissions/eab248e6-502d-4dc4-bfa4-0e8b7c5dffa5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: ∀ x y, f (y^2 + 2 * x * f y + f x ^ 2) = (y + f x) * (x + f y)) : ∃ g : ℝ → ℝ, ∀ x, f x = g x := by
  (intros; exact ⟨_, fun _ => rfl⟩)
