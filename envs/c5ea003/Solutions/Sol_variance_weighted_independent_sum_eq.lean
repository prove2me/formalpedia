-- Prove2me | solution 1 for variance_weighted_independent_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-23T23:37:00.027977+00:00
-- url     : https://prove2.me/submissions/1540a549-a9e8-4e4d-b3cc-059a33f308fb

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    (X : ι → Ω → ℝ) (coeff : ι → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hindep : Set.Pairwise Set.univ (fun i j => IndepFun (X i) (X j) μ)) :
    variance (fun ω => ∑ i, coeff i * X i ω) μ
      = ∑ i, (coeff i) ^ 2 * variance (X i) μ := by
  classical
  have hrw : (fun ω => ∑ i, coeff i * X i ω)
      = ∑ i, (fun ω => coeff i * X i ω) := by
    funext ω; simp [Finset.sum_apply]
  rw [hrw]
  have hY : ∀ i ∈ (Finset.univ : Finset ι),
      MemLp (fun ω => coeff i * X i ω) 2 μ := by
    intro i _
    simpa using (hX i).const_mul (coeff i)
  have hYindep : Set.Pairwise (↑(Finset.univ : Finset ι))
      (fun i j => IndepFun (fun ω => coeff i * X i ω) (fun ω => coeff j * X j ω) μ) := by
    intro i _ j _ hij
    have := hindep (Set.mem_univ i) (Set.mem_univ j) hij
    exact this.comp (measurable_const_mul (coeff i)) (measurable_const_mul (coeff j))
  rw [IndepFun.variance_sum hY hYindep]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [variance_const_mul]
