-- Prove2me | solution 1 for MarkovChainCLT.exists_iterKernel_pos_of_harrisErgodic
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-04T20:12:37.475438+00:00
-- url     : https://prove2.me/submissions/c9314479-539f-4faf-898f-517e2b698039

import Theorems.Thm_MarkovChainCLT_tendsto_iterKernel_apply_toReal_of_harrisErgodic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*}
    [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P] (π : Measure X)
    [IsProbabilityMeasure π] (hP : HarrisErgodic P π) (A : Set X) (hA : MeasurableSet A)
    (hπA : 0 < π A) (x : X) :
    ∃ n : ℕ, 0 < (iterKernel P n) x A := by
  have hlim := tendsto_iterKernel_apply_toReal_of_harrisErgodic P π hP x A hA
  have hpos : (0 : ℝ) < (π A).toReal :=
    ENNReal.toReal_pos hπA.ne' (measure_ne_top _ _)
  obtain ⟨n, hn⟩ := (hlim.eventually_const_lt hpos).exists
  exact ⟨n, (ENNReal.toReal_pos_iff.mp hn).1⟩
