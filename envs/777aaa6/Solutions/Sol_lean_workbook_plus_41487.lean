-- Prove2me | solution 1 for lean_workbook_plus_41487
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:26.093852+00:00
-- url     : https://prove2.me/submissions/17b97b2e-cb6e-44d0-acc2-05e7fb97f4e9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∃ x : ℕ → ℝ, x 2 = 0 ∧ x 3 = 0 ∧ x 2015 = 0 ∧ x 1 = 1 := by
  let f : ℕ → ℝ := fun n => if n=1 then 1 else 0
  have sourceAll (n : ℕ) (hn : n≠1) : f n=0 := by simp [f,hn]
  refine ⟨f,sourceAll 2 (by decide),sourceAll 3 (by decide),sourceAll 2015 (by decide),?_⟩
  simp [f]
