-- Prove2me | solution 1 for MarkovChainCLT.stationary_mean_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:43:47.342511+00:00
-- url     : https://prove2.me/submissions/707d0fcb-c0f3-437f-a0ff-7849c3c83d21

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) :
    ∀ k : ℕ, ∫ ω, Y k ω ∂P = 0 := by
  intro k
  have hmap : P.map (Y k) = P.map (Y 0) := by
    have h := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (hstat k)
    rw [Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY (n + k)),
      Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY n)] at h
    simpa [Function.comp_def] using h
  have h1 : ∫ x, x ∂(P.map (Y k)) = ∫ ω, Y k ω ∂P :=
    integral_map (hY k).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
  have h2 : ∫ x, x ∂(P.map (Y 0)) = ∫ ω, Y 0 ω ∂P :=
    integral_map (hY 0).aemeasurable (f := fun x : ℝ => x) (by fun_prop)
  rw [← h1, hmap, h2, hcent]
