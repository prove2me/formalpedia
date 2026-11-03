-- Prove2me | Theorems.Thm_levy_foundations_smallJumpIntegralLpIncrement
-- name    : levy_foundations_smallJumpIntegralLpIncrement
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T18:10:07.331996+00:00
-- url     : https://prove2.me/theorems/1be9ccc2-4753-453d-9ef3-646e70c12961
-- title:
--   Compensated small-jump increments equal band integrals
-- statement:
--   For 0≤s≤t the increment of the small-jump integral is the compensated integral of the indicator of the disjoint time band (s,t]. This is the bridge from the L² construction to independent martingale increments.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently authored Prove2Me draft pending exact-revision remote compiler verification. TimeSpacePoisson.lean lines 284–307.

import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_levy_foundations_smallJumpIntegralLp
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension

open MeasureTheory

theorem levy_foundations_smallJumpIntegralLpIncrement
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure ℝ)
    [SigmaFinite ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → ℝ × ℝ)
    (I : Lp ℝ 2 (volume.prod ν) → Lp ℝ 2 μ)
    (hI : LevyFoundations.IsCompensatedPoissonL2Extension
      (volume.prod ν) μ K X I)
    (hν : LevyFoundations.isLevyMeasure ν)
    (s t : ℝ) (h0 : 0 ≤ s) (hst : s ≤ t) :
    LevyFoundations.smallJumpIntegralLp ν μ I hν t -
      LevyFoundations.smallJumpIntegralLp ν μ I hν s =
    I (by
      classical
      let f : ℝ × ℝ → ℝ :=
        (Set.Ioc s t ×ˢ Set.Ioo (-1) 1).indicator (fun p => p.2)
      exact if h : MemLp f 2 (volume.prod ν) then h.toLp f else 0) := by sorry
