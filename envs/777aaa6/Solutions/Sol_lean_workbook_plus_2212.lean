-- Prove2me | solution 1 for lean_workbook_plus_2212
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:04:06.055189+00:00
-- url     : https://prove2.me/submissions/80eed4bf-1ad1-49c6-8eb6-04a457ed6a2a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (k : ℤ) : (x < ⌊x⌋ + 1) ∧ (⌈x⌉ < x + 1) ∧ (⌊k + x⌋ = k + ⌊x⌋) ∧ (⌊x⌋ = -⌈-x⌉) ∧ (⌈x⌉ = -⌊-x⌋) := by
  exact ⟨Int.lt_floor_add_one x,Int.ceil_lt_add_one x,Int.floor_intCast_add k x,by rw [Int.ceil_neg,neg_neg],by rw [Int.floor_neg,neg_neg]⟩
