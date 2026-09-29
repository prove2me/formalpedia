-- Prove2me | solution 1 for bernoulli_cube_linear_functional_variance_eq
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-23T23:37:00.672769+00:00
-- url     : https://prove2.me/submissions/91f73a5b-b8db-4d41-9289-bab93aa21e94

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem solution
    {ι : Type*} [Fintype ι] (p : ℝ≥0) (h : p ≤ 1) (coeff : ι → ℝ) :
    variance (fun ω : ι → Bool => ∑ i, coeff i * (cond (ω i) 1 0 : ℝ))
        (Measure.pi (fun _ : ι => (PMF.bernoulli p h).toMeasure))
      = (∑ i, (coeff i) ^ 2) * ((p : ℝ) * (1 - p)) := by
  classical
  -- per-coordinate Bernoulli-indicator variance = p(1-p)
  have hbase : variance (fun b : Bool => (cond b 1 0 : ℝ)) (PMF.bernoulli p h).toMeasure
      = (p : ℝ) * (1 - p) := by
    have hmeas : AEStronglyMeasurable (fun b : Bool => (cond b 1 0 : ℝ))
        (PMF.bernoulli p h).toMeasure :=
      (measurable_of_finite _).aestronglyMeasurable
    have hf : MemLp (fun b : Bool => (cond b 1 0 : ℝ)) 2 (PMF.bernoulli p h).toMeasure :=
      MemLp.of_bound hmeas 1 (.of_forall fun b => by cases b <;> simp)
    rw [variance_eq_sub hf]
    have hEf : (PMF.bernoulli p h).toMeasure[fun b : Bool => (cond b 1 0 : ℝ)] = (p : ℝ) := by
      simpa using PMF.bernoulli_expectation h
    have hfsq : (fun b : Bool => ((fun b : Bool => (cond b 1 0 : ℝ)) ^ 2) b)
        = (fun b : Bool => (cond b 1 0 : ℝ)) := by
      funext b; cases b <;> simp
    have hEfsq : (PMF.bernoulli p h).toMeasure[(fun b : Bool => (cond b 1 0 : ℝ)) ^ 2]
        = (p : ℝ) := by
      rw [hfsq]; exact hEf
    rw [hEfsq, hEf]; ring
  -- per-coordinate weighted-indicator functions
  set X : ι → Bool → ℝ := fun i b => coeff i * (cond b 1 0 : ℝ) with hXdef
  have hX : ∀ i, MemLp (X i) 2 (PMF.bernoulli p h).toMeasure := by
    intro i
    have hmeas : AEStronglyMeasurable (X i) (PMF.bernoulli p h).toMeasure :=
      (measurable_of_finite _).aestronglyMeasurable
    exact MemLp.of_bound hmeas (|coeff i|)
      (.of_forall fun b => by cases b <;> simp [hXdef, abs_nonneg])
  have halign : (fun ω : ι → Bool => ∑ i, coeff i * (cond (ω i) 1 0 : ℝ))
      = ∑ i, fun ω : ι → Bool => X i (ω i) := by
    funext ω; simp [hXdef, Finset.sum_apply]
  rw [halign, variance_sum_pi hX]
  have hper : ∀ i, variance (X i) (PMF.bernoulli p h).toMeasure
      = (coeff i) ^ 2 * ((p : ℝ) * (1 - p)) := by
    intro i
    have hcm : variance (X i) (PMF.bernoulli p h).toMeasure
        = (coeff i) ^ 2 * variance (fun b : Bool => (cond b 1 0 : ℝ))
            (PMF.bernoulli p h).toMeasure := by
      simpa [hXdef] using variance_const_mul (coeff i)
        (fun b : Bool => (cond b 1 0 : ℝ)) (PMF.bernoulli p h).toMeasure
    rw [hcm, hbase]
  simp_rw [hper]
  rw [← Finset.sum_mul]
