-- Prove2me | solution 1 for lean_workbook_plus_768
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:06:58.016471+00:00
-- url     : https://prove2.me/submissions/7bd78761-f031-4e4c-905f-49eff33baafd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ → ℝ):(∀ x y, f (x * y) = x * f y) ↔ ∃ l:ℝ, ∀ x, f x = x * l := by
  constructor
  · intro h
    refine ⟨f 1,?_⟩
    intro x
    simpa using h x 1
  · rintro ⟨l,hl⟩ x y
    rw [hl,hl]
    ring
