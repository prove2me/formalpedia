-- Prove2me | solution 1 for MarkovChainCLT.stationary_memLp_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:44:52.147168+00:00
-- url     : https://prove2.me/submissions/7c4b91ca-c6b9-4e06-8d1a-fad0d4dda800

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hL2 : MemLp (Y 0) 2 P) :
    ∀ k : ℕ, MemLp (Y k) 2 P := by
  intro k
  have hmap : P.map (Y k) = P.map (Y 0) := by
    have h := congrArg (Measure.map (fun f : ℕ → ℝ => f 0)) (hstat k)
    rw [Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY (n + k)),
      Measure.map_map (measurable_pi_apply 0)
        (measurable_pi_lambda _ fun n => hY n)] at h
    simpa [Function.comp_def] using h
  have h0 : MemLp (id : ℝ → ℝ) 2 (P.map (Y 0)) :=
    (memLp_map_measure_iff (measurable_id.aestronglyMeasurable)
      (hY 0).aemeasurable).2 hL2
  have hk : MemLp (id : ℝ → ℝ) 2 (P.map (Y k)) := by
    rw [hmap]
    exact h0
  exact (memLp_map_measure_iff (measurable_id.aestronglyMeasurable)
    (hY k).aemeasurable).1 hk
