-- Prove2me | solution 1 for ProbabilityTheory.cov_indicator_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-05T00:04:26.179576+00:00
-- url     : https://prove2.me/submissions/e9606833-4626-4f02-9151-7a53eb4c2e28

import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    cov[Set.indicator A (fun _ => (1 : ℝ)), Set.indicator B (fun _ => (1 : ℝ)); P]
      = (P (A ∩ B)).toReal - (P A).toReal * (P B).toReal := by
  have hbdA : ∀ᵐ ω ∂P, ‖Set.indicator A (fun _ => (1 : ℝ)) ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · rw [Set.indicator_of_mem hω]
      simp
    · rw [Set.indicator_of_notMem hω]
      simp
  have h1A : MemLp (Set.indicator A (fun _ => (1 : ℝ))) 2 P :=
    MemLp.of_bound ((measurable_const).indicator hA).aestronglyMeasurable 1 hbdA
  have hbdB : ∀ᵐ ω ∂P, ‖Set.indicator B (fun _ => (1 : ℝ)) ω‖ ≤ 1 := by
    filter_upwards with ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      simp
    · rw [Set.indicator_of_notMem hω]
      simp
  have h1B : MemLp (Set.indicator B (fun _ => (1 : ℝ))) 2 P :=
    MemLp.of_bound ((measurable_const).indicator hB).aestronglyMeasurable 1 hbdB
  rw [covariance_eq_sub h1A h1B]
  have eA : P[Set.indicator A (fun _ => (1 : ℝ))] = (P A).toReal := by
    rw [integral_indicator_const _ hA]
    simp [Measure.real_def]
  have eB : P[Set.indicator B (fun _ => (1 : ℝ))] = (P B).toReal := by
    rw [integral_indicator_const _ hB]
    simp [Measure.real_def]
  have eAB : P[Set.indicator A (fun _ => (1 : ℝ)) * Set.indicator B (fun _ => (1 : ℝ))]
      = (P (A ∩ B)).toReal := by
    have hmul : (Set.indicator A (fun _ => (1 : ℝ)) * Set.indicator B (fun _ => (1 : ℝ)))
        = Set.indicator (A ∩ B) (fun _ => (1 : ℝ)) := by
      funext ω
      simp only [Pi.mul_apply]
      by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]
    rw [hmul, integral_indicator_const _ (hA.inter hB)]
    simp [Measure.real_def]
  rw [eA, eB, eAB]
