-- Prove2me | solution 1 for lean_workbook_plus_43634
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:01:40.893407+00:00
-- url     : https://prove2.me/submissions/3ea6bc1b-fbfd-472f-91f1-787c91b3f519

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f : ℝ → ℝ): (∀ x y, f (x + y) = f x + y) ↔ ∃ a, ∀ x, f x = x + a := by
  constructor
  · intro h
    refine ⟨f 0,?_⟩
    intro x
    simpa [add_comm] using h 0 x
  · rintro ⟨a,ha⟩ x y
    rw [ha,ha]
    ring
