-- Prove2me | solution 1 for lean_workbook_plus_74363
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:22:12.241856+00:00
-- url     : https://prove2.me/submissions/0f4db002-3e78-47b6-be3d-fd250f626e7e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
set_option autoImplicit false
set_option maxHeartbeats 500000
theorem solution : ∃ f : ℝ → ℝ, ∀ x ∈ Set.Icc 0 (1 / 8), f x = 0 ∧ ∀ x ≥ 1 / 8, f x = (8 * x - 1) / 14   :=  by
  refine ⟨fun x => if x ≤ 1 / 8 then 0 else (8 * x - 1) / 14, ?_⟩
  intro x hx
  constructor
  · change (if x ≤ (1/8:ℝ) then (0:ℝ) else (8*x-1)/14) = 0
    exact if_pos hx.2
  · intro y hy
    change (if y ≤ (1/8:ℝ) then (0:ℝ) else (8*y-1)/14) = (8*y-1)/14
    split_ifs with h
    · have : y = 1 / 8 := le_antisymm h hy
      subst y
      norm_num
    · rfl
#print axioms solution
