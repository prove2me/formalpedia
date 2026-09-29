-- Prove2me | solution 1 for Erdos180.projectiveDirection_nonzero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:06:12.874819+00:00
-- url     : https://prove2.me/submissions/d133f078-7388-4f1a-963f-e29557a2ab08

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Push

open Erdos180
variable (K : Type*) [Field K]

theorem solution
    {x y x' y' : K}
    (hdet : x * y' - x' * y ≠ 0) :
    x ≠ 0 ∨ y ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  apply hdet
  simp [hx, hy]
