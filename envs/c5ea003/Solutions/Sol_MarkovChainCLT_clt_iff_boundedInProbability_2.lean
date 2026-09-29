-- Prove2me | solution 2 for MarkovChainCLT.clt_iff_boundedInProbability
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T00:43:04.370226+00:00
-- url     : https://prove2.me/submissions/d42bd29b-019d-4507-8f18-2952b43cfde3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MixingCoefficients
import Theorems.Thm_MarkovChainCLT_boundedInProbability_of_tendstoInDistribution
import Theorems.Thm_MarkovChainCLT_clt_of_boundedInProbability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

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
  · rintro ⟨v, hconv⟩
    exact boundedInProbability_of_tendstoInDistribution
      (chainMeasure P π) (gaussianReal 0 v)
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * sampleAvg f n ω)
      (id : ℝ → ℝ) hconv
  · intro hbdd
    exact clt_of_boundedInProbability P π hP f hf hcent hL2 hbdd
