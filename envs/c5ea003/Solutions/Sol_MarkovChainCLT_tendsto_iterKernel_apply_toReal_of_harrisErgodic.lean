-- Prove2me | solution 1 for MarkovChainCLT.tendsto_iterKernel_apply_toReal_of_harrisErgodic
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-04T20:11:34.608405+00:00
-- url     : https://prove2.me/submissions/dac15541-9260-49b8-842d-d8a11a78f641

import Definitions.Def_MarkovErgodicity

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

/-- The total variation distance dominates the difference of the two measures on any
measurable set, for finite measures (the supremum defining `tvDist` is attained over a set
bounded by the sum of the total masses). -/
private lemma abs_sub_le_tvDist {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : Set X) (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ tvDist μ ν := by
  unfold tvDist
  apply le_csSup
  · refine ⟨(μ Set.univ).toReal + (ν Set.univ).toReal, ?_⟩
    rintro r ⟨B, hB, rfl⟩
    calc |(μ B).toReal - (ν B).toReal|
        ≤ |(μ B).toReal| + |(ν B).toReal| := abs_sub _ _
      _ = (μ B).toReal + (ν B).toReal := by
          rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ (μ Set.univ).toReal + (ν Set.univ).toReal :=
          add_le_add
            (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono (Set.subset_univ B)))
            (ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Set.subset_univ B)))
  · exact ⟨A, hA, rfl⟩

theorem solution {X : Type*}
    [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hP : HarrisErgodic P π) (x : X) (A : Set X)
    (hA : MeasurableSet A) :
    Tendsto (fun n => ((iterKernel P n) x A).toReal) atTop (𝓝 (π A).toReal) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (hP.2 x)
  rw [Real.norm_eq_abs]
  exact abs_sub_le_tvDist _ _ A hA
