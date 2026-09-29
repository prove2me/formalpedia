-- Prove2me | solution 1 for lean_workbook_plus_23007
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:12.178001+00:00
-- url     : https://prove2.me/submissions/6f50600a-c214-4c3d-8aba-ef609203ea6e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (g : ℝ → ℝ) (h : ∀ x y, g (x + y) = g x) : ∃ c, ∀ x, g x = c := by
  refine ⟨g 0,?_⟩
  intro x
  simpa using h 0 x
