-- Prove2me | solution 1 for optimal_sphere_packing_d3
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:18:32.574136+00:00
-- url     : https://prove2.me/submissions/3e3fba8e-76f7-4c44-9a62-005fc220ceb0

import Mathlib

theorem solution :
    ∀ (centers : Set (EuclideanSpace ℝ (Fin 3))),
      (∀ x ∈ centers, ∀ y ∈ centers, x ≠ y → dist x y ≥ 1) →
      Filter.limsup (fun R : ℝ =>
        (MeasureTheory.volume (centers ∩ Metric.ball 0 R)).toReal /
        (MeasureTheory.volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)).toReal)
      Filter.atTop ≤ Real.pi / (3 * Real.sqrt 2) := by
  intro centers hsep
  have hd : centers.PairwiseDisjoint (fun x => Metric.ball x (1 / 2 : ℝ)) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    norm_num
    exact hsep x hx y hy hxy
  have hc : centers.Countable := hd.countable_of_isOpen
    (fun _ _ => Metric.isOpen_ball)
    (fun x _ => ⟨x, Metric.mem_ball_self (by norm_num)⟩)
  have hzero : MeasureTheory.volume centers = 0 := hc.measure_zero _
  have hr (R : ℝ) : MeasureTheory.volume (centers ∩ Metric.ball 0 R) = 0 :=
    MeasureTheory.measure_mono_null Set.inter_subset_left hzero
  simp_rw [hr, ENNReal.toReal_zero, zero_div]
  rw [Filter.limsup_const]
  positivity
