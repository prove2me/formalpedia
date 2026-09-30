-- Prove2me | solution 2 for lean_workbook_plus_55606
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:12:55.666689+00:00
-- url     : https://prove2.me/submissions/6d96a469-ecf8-4033-b5c8-4a8a81757f96

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem quadratic_iterate_factorization {R : Type*} [CommRing R] (b c x : R) :
    (x ^ 2 + b * x + c) ^ 2 + b * (x ^ 2 + b * x + c) + c - x =
      (x ^ 2 + (b - 1) * x + c) * (x ^ 2 + (b + 1) * x + (b + c + 1)) := by ring

noncomputable def quadraticMap (x : ℝ) : ℝ := x ^ 2 - 3 * x - 2

theorem second_iterate_identity (x : ℝ) :
    quadraticMap (quadraticMap x) - x = (x ^ 2 - 4 * x - 2) * (x ^ 2 - 2 * x - 4) := by
  unfold quadraticMap
  ring

theorem fixed_points (x : ℝ) :
    quadraticMap x = x ↔ x = 2 + Real.sqrt 6 ∨ x = 2 - Real.sqrt 6 := by
  have hr : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by positivity)
  unfold quadraticMap
  constructor
  · intro h
    have hf : (x - 2 - Real.sqrt 6) * (x - 2 + Real.sqrt 6) = 0 := by nlinarith [hr]
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> nlinarith [hr]

theorem cycle_swap :
    quadraticMap (1 + Real.sqrt 5) = 1 - Real.sqrt 5 ∧
      quadraticMap (1 - Real.sqrt 5) = 1 + Real.sqrt 5 := by
  have hr : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by positivity)
  unfold quadraticMap
  constructor <;> nlinarith [hr]

theorem cycle_distinct : (1 : ℝ) + Real.sqrt 5 ≠ 1 - Real.sqrt 5 := by
  have hp : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by positivity)
  linarith

theorem second_iterate_points (x : ℝ) :
    quadraticMap (quadraticMap x) = x ↔
      x = 2 + Real.sqrt 6 ∨ x = 2 - Real.sqrt 6 ∨
      x = 1 + Real.sqrt 5 ∨ x = 1 - Real.sqrt 5 := by
  have hr : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by positivity)
  constructor
  · intro h
    have hf : (x ^ 2 - 4 * x - 2) * (x ^ 2 - 2 * x - 4) = 0 := by
      rw [← second_iterate_identity, h]
      ring
    rcases mul_eq_zero.mp hf with hfix | hcycle
    · have he : quadraticMap x = x := by unfold quadraticMap; nlinarith [hfix]
      rcases (fixed_points x).mp he with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hc : (x - 1 - Real.sqrt 5) * (x - 1 + Real.sqrt 5) = 0 := by nlinarith [hr]
      rcases mul_eq_zero.mp hc with h | h
      · exact Or.inr (Or.inr (Or.inl (by linarith)))
      · exact Or.inr (Or.inr (Or.inr (by linarith)))
  · rintro (h | h | h | h)
    · have he := (fixed_points x).mpr (Or.inl h)
      rw [he, he]
    · have he := (fixed_points x).mpr (Or.inr h)
      rw [he, he]
    · rw [h, cycle_swap.1, cycle_swap.2]
    · rw [h, cycle_swap.2, cycle_swap.1]

theorem genuine_two_cycle (x : ℝ) :
    (quadraticMap (quadraticMap x) = x ∧ quadraticMap x ≠ x) ↔
      x = 1 + Real.sqrt 5 ∨ x = 1 - Real.sqrt 5 := by
  constructor
  · rintro ⟨h, hn⟩
    rcases (second_iterate_points x).mp h with h | h | h | h
    · exact False.elim (hn ((fixed_points x).mpr (Or.inl h)))
    · exact False.elim (hn ((fixed_points x).mpr (Or.inr h)))
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · refine ⟨?_, ?_⟩
      · rw [cycle_swap.1, cycle_swap.2]
      · rw [cycle_swap.1]
        exact Ne.symm cycle_distinct
    · refine ⟨?_, ?_⟩
      · rw [cycle_swap.2, cycle_swap.1]
      · rw [cycle_swap.2]
        exact cycle_distinct

theorem solution (x : ℝ) :
    (x ^ 2 - 3 * x - 2) ^ 2 - 3 * (x ^ 2 - 3 * x - 2) - 2 - x =
      (x ^ 2 - 4 * x - 2) * (x ^ 2 - 2 * x - 4) := by
  exact second_iterate_identity x
