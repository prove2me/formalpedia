-- Prove2me | solution 1 for lean_workbook_plus_17848
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:31.683276+00:00
-- url     : https://prove2.me/submissions/3d3f688d-5afe-4ee7-84ca-f382d893d914

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℝ) (hx : x ≠ 0) : ∃ f : ℝ → ℝ, f (x + 1) * f x = x := by
  refine ⟨fun t => if t = x then x else 1, ?_⟩
  have h1 : x + 1 ≠ x := by linarith
  simp [h1]
