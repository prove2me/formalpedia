-- Prove2me | solution 1 for MarkovChainCLT.clt_iff_boundedInProbability
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T06:59:59.437386+00:00
-- url     : https://prove2.me/submissions/530f5ccd-07ff-4776-9505-4d380863e1f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MarkovChainCLT_boundedInProbability_of_tendstoInDistribution
import Theorems.Thm_MarkovChainCLT_clt_of_boundedInProbability

open MeasureTheory ProbabilityTheory Filter MarkovChainCLT
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hcent : ∫ x, f x ∂π = 0) (hL2 : MemLp f 2 π) :
    (∃ v : ℝ≥0, TendstoInDistribution
        (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * sampleAvg f n ω)
        atTop (id : ℝ → ℝ) (fun _ => chainMeasure P π) (gaussianReal 0 v))
      ↔ BoundedInProbability
          (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * sampleAvg f n ω)
          (chainMeasure P π) := by
  constructor
  · rintro ⟨v, hv⟩
    exact MarkovChainCLT.boundedInProbability_of_tendstoInDistribution
      (chainMeasure P π) (gaussianReal 0 v) _ (id : ℝ → ℝ) hv
  · intro hbdd
    exact MarkovChainCLT.clt_of_boundedInProbability P π hP f hf hcent hL2 hbdd
