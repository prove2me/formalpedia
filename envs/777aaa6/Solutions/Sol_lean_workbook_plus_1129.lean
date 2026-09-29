-- Prove2me | solution 1 for lean_workbook_plus_1129
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:36:10.073332+00:00
-- url     : https://prove2.me/submissions/f73778b6-d7e0-4255-ac7d-0a8b9177359d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 1) : (1 + a) * (1 + b^2) * (1 + c) ≥ 50 / 27 ∧ (a = 0 ∧ b = 1 / 3 ∧ c = 2 / 3 ∨ a = 2 / 3 ∧ b = 1 / 3 ∧ c = 0) ↔ a = 0 ∧ b = 1 / 3 ∧ c = 2 / 3 ∨ a = 2 / 3 ∧ b = 1 / 3 ∧ c = 0 := by
  have hb1 : b ≤ 1 := by linarith
  have hcEq : c=1-a-b := by linarith
  have hid : (1+a)*(1+b^2)*(1+c)-50/27 = (b-1/3)^2*(4/3-b)+a*c*(1+b^2) := by
    rw [hcEq]
    ring
  have hbound : (1+a)*(1+b^2)*(1+c) ≥ 50/27 := by
    have hfirst := mul_nonneg (sq_nonneg (b-1/3)) (by linarith : 0 ≤ 4/3-b)
    have hsecond : 0 ≤ a*c*(1+b^2) := by positivity
    linarith
  have heqCases (hcase : a=0 ∧ b=1/3 ∧ c=2/3 ∨ a=2/3 ∧ b=1/3 ∧ c=0) : (1+a)*(1+b^2)*(1+c)=50/27 := by
    rcases hcase with ⟨rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl⟩ <;> norm_num <;> rfl
  constructor
  · exact fun h => h.2
  · intro hcase
    refine ⟨?_,hcase⟩
    rw [heqCases hcase] at hbound ⊢ <;> exact hbound
