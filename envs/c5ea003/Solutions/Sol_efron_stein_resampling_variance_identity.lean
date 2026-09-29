-- Prove2me | solution 1 for efron_stein_resampling_variance_identity
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-23T23:36:38.824364+00:00
-- url     : https://prove2.me/submissions/7dbaff38-3832-4370-b863-1ba606250f5a

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.IdentDistrib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {W W' : Ω → ℝ}
    (hW : MemLp W 2 μ) (hW' : MemLp W' 2 μ)
    (hindep : IndepFun W W' μ) (hident : IdentDistrib W W' μ μ) :
    variance W μ = (∫ ω, (W ω - W' ω) ^ 2 ∂μ) / 2 := by
  have hWm : AEStronglyMeasurable W μ := hW.aestronglyMeasurable
  have hW'm : AEStronglyMeasurable W' μ := hW'.aestronglyMeasurable
  have hWint : Integrable W μ := hW.integrable one_le_two
  have hW'int : Integrable W' μ := hW'.integrable one_le_two
  have hWsq : Integrable (fun ω => W ω ^ 2) μ := by
    simpa [pow_two] using hW.integrable_sq
  have hW'sq : Integrable (fun ω => W' ω ^ 2) μ := by
    simpa [pow_two] using hW'.integrable_sq
  have hWW' : Integrable (fun ω => W ω * W' ω) μ :=
    hindep.integrable_mul hWint hW'int
  have hexpand : ∀ ω, (W ω - W' ω) ^ 2
      = W ω ^ 2 - 2 * (W ω * W' ω) + W' ω ^ 2 := by
    intro ω; ring
  have hsplit : ∫ ω, (W ω - W' ω) ^ 2 ∂μ
      = (∫ ω, W ω ^ 2 ∂μ) - 2 * (∫ ω, W ω * W' ω ∂μ) + (∫ ω, W' ω ^ 2 ∂μ) := by
    calc ∫ ω, (W ω - W' ω) ^ 2 ∂μ
        = ∫ ω, (W ω ^ 2 - 2 * (W ω * W' ω) + W' ω ^ 2) ∂μ := by
          simp_rw [hexpand]
      _ = (∫ ω, (W ω ^ 2 - 2 * (W ω * W' ω)) ∂μ) + ∫ ω, W' ω ^ 2 ∂μ :=
          integral_add (hWsq.sub (hWW'.const_mul 2)) hW'sq
      _ = ((∫ ω, W ω ^ 2 ∂μ) - ∫ ω, 2 * (W ω * W' ω) ∂μ) + ∫ ω, W' ω ^ 2 ∂μ := by
          rw [integral_sub hWsq (hWW'.const_mul 2)]
      _ = (∫ ω, W ω ^ 2 ∂μ) - 2 * (∫ ω, W ω * W' ω ∂μ) + (∫ ω, W' ω ^ 2 ∂μ) := by
          rw [integral_const_mul]
  have hmul : ∫ ω, W ω * W' ω ∂μ = (∫ ω, W ω ∂μ) * (∫ ω, W' ω ∂μ) :=
    hindep.integral_fun_mul_eq_mul_integral hWm hW'm
  have hEeq : ∫ ω, W' ω ∂μ = ∫ ω, W ω ∂μ := (hident.symm.integral_eq)
  have hEsq : ∫ ω, W' ω ^ 2 ∂μ = ∫ ω, W ω ^ 2 ∂μ := by
    have := (hident.symm.comp (measurable_id.pow_const 2)).integral_eq
    simpa using this
  rw [variance_eq_sub hW]
  rw [hsplit, hmul, hEeq, hEsq]
  have hsq : μ[W ^ 2] = ∫ ω, W ω ^ 2 ∂μ := by simp [Pi.pow_apply]
  have hEW : μ[W] = ∫ ω, W ω ∂μ := rfl
  rw [hsq, hEW]
  ring
