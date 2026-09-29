-- Prove2me | solution 1 for lean_workbook_plus_34929
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:17:37.39449+00:00
-- url     : https://prove2.me/submissions/43cebf1e-aea5-48ff-b691-c02d2df72c1a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (f : ℝ → ℝ) (hf: a ≠ 0) (hf2: ∀ x y, a^2 * f (x * y + f y) = f (f x) * f y + a^4 * y): ∃ g: ℝ → ℝ, ∀ x, f x = g x := by
  (intros; exact ⟨_, fun _ => rfl⟩)
