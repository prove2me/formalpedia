-- Prove2me | solution 1 for MarkovChainCLT.processSigma_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T15:40:54.897786+00:00
-- url     : https://prove2.me/submissions/fc069635-7088-4561-8684-58a85ad86ec9

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {Ω X E : Type*} [MeasurableSpace X]
    [MeasurableSpace E] (Y : ℕ → Ω → X) (g : X → E) (hg : Measurable g) (s : Set ℕ) :
    processSigma (fun i ω => g (Y i ω)) s ≤ processSigma Y s := by
  refine iSup₂_mono fun i _ => ?_
  have h : MeasurableSpace.comap (fun ω => g (Y i ω)) inferInstance
      = MeasurableSpace.comap (Y i) (MeasurableSpace.comap g inferInstance) := by
    rw [MeasurableSpace.comap_comp]; rfl
  rw [h]
  exact MeasurableSpace.comap_mono hg.comap_le
