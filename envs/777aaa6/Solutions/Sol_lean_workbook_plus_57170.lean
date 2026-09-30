-- Prove2me | solution 1 for lean_workbook_plus_57170
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:37:48.08835+00:00
-- url     : https://prove2.me/submissions/f9f33cb4-62bd-4cb4-8a42-ec25668d70d4

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

theorem fifth_refinement (x : ℝ) (hx : -2 ≤ x) :
    3 * (x ^ 3 - x ^ 2) ≤ x ^ 5 - x ^ 2 := by
  have hp := mul_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg (x - 1)))
    (show 0 ≤ x + 2 by linarith)
  nlinarith [hp]

theorem finite_fifth_refinement {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, -2 ≤ f i) :
    3 * ((∑ i ∈ s, f i ^ 3) - ∑ i ∈ s, f i ^ 2) ≤
      (∑ i ∈ s, f i ^ 5) - ∑ i ∈ s, f i ^ 2 := by
  have h := Finset.sum_le_sum fun i hi => fifth_refinement (f i) (hf i hi)
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum] using h

theorem finite_fifth_comparison {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, -2 ≤ f i)
    (h : (∑ i ∈ s, f i ^ 2) ≤ ∑ i ∈ s, f i ^ 3) :
    (∑ i ∈ s, f i ^ 2) ≤ ∑ i ∈ s, f i ^ 5 := by
  have hr := finite_fifth_refinement s f hf
  linarith

theorem fifth_refinement_equality (x : ℝ) (hx : -2 < x) :
    x ^ 5 - x ^ 2 = 3 * (x ^ 3 - x ^ 2) ↔ x = 0 ∨ x = 1 := by
  constructor
  · intro he
    have hp : x ^ 2 * (x - 1) ^ 2 * (x + 2) = 0 := by nlinarith [he]
    have hq := (mul_eq_zero.mp hp).resolve_right (ne_of_gt (by linarith))
    rcases mul_eq_zero.mp hq with h | h
    · exact Or.inl (sq_eq_zero_iff.mp h)
    · exact Or.inr (by have hh := sq_eq_zero_iff.mp h; linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem source_equality (x y z : ℝ) (hx : -1 < x) (hy : -1 < y)
    (hz : -1 < z) (h : x ^ 2 + y ^ 2 + z ^ 2 ≤ x ^ 3 + y ^ 3 + z ^ 3) :
    x ^ 5 + y ^ 5 + z ^ 5 = x ^ 2 + y ^ 2 + z ^ 2 ↔
      (x = 0 ∨ x = 1) ∧ (y = 0 ∨ y = 1) ∧ (z = 0 ∨ z = 1) := by
  have rx := fifth_refinement x (by linarith)
  have ry := fifth_refinement y (by linarith)
  have rz := fifth_refinement z (by linarith)
  constructor
  · intro he
    exact ⟨(fifth_refinement_equality x (by linarith)).mp (by linarith),
      (fifth_refinement_equality y (by linarith)).mp (by linarith),
      (fifth_refinement_equality z (by linarith)).mp (by linarith)⟩
  · rintro ⟨hx | hx, hy | hy, hz | hz⟩ <;> subst_vars <;> norm_num

theorem solution (x y z : ℝ) (hx : x > -1) (hy : y > -1) (hz : z > -1)
    (h : x ^ 3 + y ^ 3 + z ^ 3 ≥ x ^ 2 + y ^ 2 + z ^ 2) :
    x ^ 5 + y ^ 5 + z ^ 5 ≥ x ^ 2 + y ^ 2 + z ^ 2 := by
  have rx := fifth_refinement x (by linarith)
  have ry := fifth_refinement y (by linarith)
  have rz := fifth_refinement z (by linarith)
  linarith
