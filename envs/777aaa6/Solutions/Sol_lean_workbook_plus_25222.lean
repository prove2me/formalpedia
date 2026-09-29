-- Prove2me | solution 1 for lean_workbook_plus_25222
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:23.166501+00:00
-- url     : https://prove2.me/submissions/7b37ae25-8b47-4f8b-b579-fdf497d91317

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ → ℝ) (hf : Function.Surjective f) (h : ∀ x, f (f x) = 2018 * f x) : ∃ y, f y = 2018 * y := by
  have he : ∀y, f y=2018*y := by
    intro y
    rcases hf y with ⟨x,hx⟩
    simpa only [hx] using h x
  exact ⟨0,he 0⟩
