-- Prove2me | solution 1 for integral_condVar_le_integral_sq_sub_of_strongly_measurable
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-24T01:48:08.189209+00:00
-- url     : https://prove2.me/submissions/b4059c55-dfa9-4eda-ac9f-8e6fd14f7123

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem solution
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hYm : StronglyMeasurable[m] Y) :
    μ[Var[X; μ | m]] ≤ ∫ ω, (X ω - Y ω) ^ 2 ∂μ := by
  -- pointwise conditional L²-minimizer bound: Var(X|m) ≤ E[(X-Y)²|m]
  have hpt : Var[X; μ | m] ≤ᵐ[μ] μ[(fun ω => (X ω - Y ω) ^ 2) | m] := by
    have heq : Var[fun ω => X ω - Y ω; μ | m] =ᵐ[μ] Var[X; μ | m] := by
      have hXint : Integrable X μ := hX.integrable one_le_two
      have hYint : Integrable Y μ := hY.integrable one_le_two
      have hcondsub : μ[(fun ω => X ω - Y ω) | m] =ᵐ[μ] fun ω => (μ[X | m]) ω - Y ω := by
        have hXYfun : (fun ω => X ω - Y ω) = X - Y := by funext ω; simp [Pi.sub_apply]
        have h1 : μ[(X - Y) | m] =ᵐ[μ] μ[X | m] - μ[Y | m] := condExp_sub hXint hYint _
        have h2 : μ[Y | m] = Y := condExp_of_stronglyMeasurable hm hYm hYint
        rw [hXYfun]
        filter_upwards [h1] with ω hω1
        simp only [Pi.sub_apply] at hω1 ⊢
        rw [hω1, h2]
      rw [condVar, condVar]
      refine condExp_congr_ae ?_
      filter_upwards [hcondsub] with ω hω
      simp only [Pi.pow_apply, Pi.sub_apply] at hω ⊢
      rw [hω]; ring
    have hXY : MemLp (fun ω => X ω - Y ω) 2 μ := by
      have : MemLp (X - Y) 2 μ := hX.sub hY
      simpa [Pi.sub_apply] using this
    have hle : Var[fun ω => X ω - Y ω; μ | m] ≤ᵐ[μ]
        μ[(fun ω => X ω - Y ω) ^ 2 | m] := condVar_ae_le_condExp_sq hm hXY
    have hsq : (fun ω => X ω - Y ω) ^ 2 = (fun ω => (X ω - Y ω) ^ 2) := by
      funext ω; simp [Pi.pow_apply]
    rw [hsq] at hle
    filter_upwards [heq, hle] with ω hω1 hω2
    rw [← hω1]; exact hω2
  have hXY : MemLp (fun ω => X ω - Y ω) 2 μ := by
    have : MemLp (X - Y) 2 μ := hX.sub hY
    simpa [Pi.sub_apply] using this
  have hsqint : Integrable (fun ω => (X ω - Y ω) ^ 2) μ := by
    have := hXY.integrable_sq
    simpa [pow_two] using this
  calc μ[Var[X; μ | m]]
      = ∫ ω, Var[X; μ | m] ω ∂μ := rfl
    _ ≤ ∫ ω, (μ[(fun ω => (X ω - Y ω) ^ 2) | m]) ω ∂μ := by
        apply integral_mono_ae integrable_condVar integrable_condExp hpt
    _ = ∫ ω, (X ω - Y ω) ^ 2 ∂μ := integral_condExp hm
