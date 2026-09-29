-- Prove2me | solution 1 for lean_workbook_plus_55943
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:23.558068+00:00
-- url     : https://prove2.me/submissions/ab08b092-f4fd-4af1-947c-8b621f30e7e0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∃ f : ℝ → ℝ, f 0 = 1 ∧ ∀ x > 0, f x = 0 := by
  refine ⟨fun x => if x=0 then 1 else 0,by simp,?_⟩
  intro x hx
  simp [ne_of_gt hx]
