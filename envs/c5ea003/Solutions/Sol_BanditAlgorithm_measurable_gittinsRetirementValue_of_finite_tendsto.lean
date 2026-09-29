-- Prove2me | solution 1 for BanditAlgorithm.measurable_gittinsRetirementValue_of_finite_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T05:09:01.8073+00:00
-- url     : https://prove2.me/submissions/063871da-605d-4cd9-92d2-babd9dc9290a

import Theorems.Thm_BanditAlgorithm_measurable_gittinsFiniteRetirementValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

open MeasureTheory ProbabilityTheory Filter Topology
open BanditAlgorithm

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    (α γ : ℝ)
    (hconv : ∀ x,
      Tendsto (fun n ↦ gittinsFiniteRetirementValue P r α γ n x)
        atTop (𝓝 (gittinsRetirementValue P r α γ x))) :
    Measurable (gittinsRetirementValue P r α γ) := by
  apply measurable_of_tendsto_metrizable
  · exact measurable_gittinsFiniteRetirementValue P hr α γ
  · rw [tendsto_pi_nhds]
    exact hconv
