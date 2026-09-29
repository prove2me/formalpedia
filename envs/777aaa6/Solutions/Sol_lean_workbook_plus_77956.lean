-- Prove2me | solution 1 for lean_workbook_plus_77956
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T06:20:51.583574+00:00
-- url     : https://prove2.me/submissions/337db554-592b-46c0-af18-2938f8c32d02

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (ha : 0 < a) : ∃ f : ℝ → ℝ, ∀ x > 0, f x = a * x := by
  exact ⟨fun x => a * x, by intros; rfl⟩
