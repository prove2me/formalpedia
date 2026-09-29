-- Prove2me | solution 1 for lean_workbook_plus_73984
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:38:31.259085+00:00
-- url     : https://prove2.me/submissions/d33e8099-cc14-4efc-a8b5-9ce776e981f7

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∃ f : ℝ → ℝ, ∀ x, (x = 0 → f x = 1) ∧ (x ≠ 0 → f x = 0) := by
  refine ⟨fun x => if x=0 then 1 else 0,?_⟩
  intro x
  constructor <;> intro h <;> simp [h]
