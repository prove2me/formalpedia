-- Prove2me | solution 1 for MarkovChainCLT.processSigma_le_of_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:54:15.435752+00:00
-- url     : https://prove2.me/submissions/dce79a8d-90bb-451b-9474-5cb6cb55d8b2

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (Y : ℕ → Ω → E) (hY : ∀ n, Measurable (Y n)) (s : Set ℕ) :
    processSigma Y s ≤ ‹MeasurableSpace Ω› := by
  unfold processSigma
  apply iSup₂_le
  intro i _
  exact measurable_iff_comap_le.1 (hY i)
