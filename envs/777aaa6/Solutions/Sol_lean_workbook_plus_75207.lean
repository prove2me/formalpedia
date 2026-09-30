-- Prove2me | solution 1 for lean_workbook_plus_75207
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:20:23.000712+00:00
-- url     : https://prove2.me/submissions/5de07c77-ee01-445a-8fe3-3c30db045206

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace RationalConstraintSharpRange

theorem exact_gap (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x * y = (x - y) / (x + 3 * y)) :
    x * (1 - 3 * y) * (1 + y) = y * (x - 1) ^ 2 := by
  have hc := (eq_div_iff (by linarith : x + 3 * y ≠ 0)).mp h
  nlinarith [hc]

theorem sharp_bound (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x * y = (x - y) / (x + 3 * y)) : y ≤ 1 / 3 := by
  have hg := exact_gap x y hx hy h
  have hp : 0 < x * (1 + y) := mul_pos hx (by linarith)
  have hn : 0 ≤ (1 - 3 * y) * (x * (1 + y)) := by
    nlinarith [mul_nonneg hy.le (sq_nonneg (x - 1))]
  have := nonneg_of_mul_nonneg_left hn hp
  linarith

theorem equality_classification (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x * y = (x - y) / (x + 3 * y)) :
    y = 1 / 3 ↔ x = 1 ∧ y = 1 / 3 := by
  constructor
  · intro he
    have hg := exact_gap x y hx hy h
    have he' : 1 - 3 * y = 0 := by linarith
    rw [he', mul_zero, zero_mul] at hg
    have hz : (x - 1) ^ 2 = 0 := (mul_eq_zero.mp hg.symm).resolve_left (ne_of_gt hy)
    exact ⟨by nlinarith [sq_nonneg (x - 1)], he⟩
  · exact And.right

theorem feasible_second_coordinate (y : ℝ) :
    (∃ x : ℝ, 0 < x ∧ 0 < y ∧ x * y = (x - y) / (x + 3 * y)) ↔
      0 < y ∧ y ≤ 1 / 3 := by
  constructor
  · rintro ⟨x, hx, hy, h⟩
    exact ⟨hy, sharp_bound x y hx hy h⟩
  · rintro ⟨hy, hy3⟩
    let f : ℝ → ℝ := fun x => x * y * (x + 3 * y) - x + y
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hleft : 0 ≤ f y := by
      dsimp [f]
      nlinarith [mul_nonneg hy.le (sq_nonneg y)]
    have hright : f 1 ≤ 0 := by
      have hp : 0 ≤ (1 - 3 * y) * (1 + y) := mul_nonneg (by linarith) (by linarith)
      dsimp [f]
      nlinarith [hp]
    obtain ⟨x, hxb, hfx⟩ := intermediate_value_Icc' (by linarith : y ≤ 1)
      hf.continuousOn (show (0 : ℝ) ∈ Set.Icc (f 1) (f y) from ⟨hright, hleft⟩)
    have hx : 0 < x := lt_of_lt_of_le hy hxb.1
    refine ⟨x, hx, hy, (eq_div_iff (by linarith : x + 3 * y ≠ 0)).mpr ?_⟩
    dsimp [f] at hfx
    linarith

theorem maximum_attained : (1 : ℝ) * (1 / 3) = (1 - 1 / 3) / (1 + 3 * (1 / 3)) := by
  ring

end RationalConstraintSharpRange

theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x * y = (x - y) / (x + 3 * y)) : y ≤ 1 / 3 :=
  RationalConstraintSharpRange.sharp_bound x y hx hy h
