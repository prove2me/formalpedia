-- Prove2me | solution 1 for Phi_max_grows
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:36:51.327698+00:00
-- url     : https://prove2.me/submissions/a6d3ca72-cda5-416d-84f4-75cba41126de

-- Sol generated from Speculative/OISCC/DynamicalSystem.lean
import Mathlib
import Definitions.Def_Speculative_OISCC_DynamicalSystem
/-
# OISCC V9.1: Dynamical System Theory
-/


noncomputable section

open Real Filter Topology Set














theorem solution(x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hmax : max x y ≥ 2) :
    max (Phi (x, y)).1 (Phi (x, y)).2 > max x y := by
  simp only [Phi]
  by_cases hxy : x ≥ y
  · have hm : max x y = x := max_eq_left hxy
    rw [hm] at hmax ⊢
    have : EML_dyn x y > x := by
      unfold EML_dyn
      nlinarith [quadratic_le_exp_of_nonneg hx.le, Real.log_le_sub_one_of_pos hy, sq_nonneg x]
    exact lt_of_lt_of_le this (le_max_left _ _)
  · push_neg at hxy
    have hm : max x y = y := max_eq_right (le_of_lt hxy)
    rw [hm] at hmax ⊢
    have : EML_dyn y x > y := by
      unfold EML_dyn
      nlinarith [quadratic_le_exp_of_nonneg hy.le, Real.log_le_sub_one_of_pos hx, sq_nonneg y]
    exact lt_of_lt_of_le this (le_max_right _ _)
