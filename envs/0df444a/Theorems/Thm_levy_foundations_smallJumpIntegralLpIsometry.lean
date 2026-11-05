-- Prove2me | Theorems.Thm_levy_foundations_smallJumpIntegralLpIsometry
-- name    : levy_foundations_smallJumpIntegralLpIsometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:08:01.369551+00:00
-- url     : https://prove2.me/theorems/c9b94078-8f10-4ff3-a71e-2ec14b5e5ebf
-- title:
--   Time-scaled L² isometry for compensated small jumps
-- statement:
--   The second moment of the compensated small-jump integral at nonnegative time t equals t times the jump-size second moment over the small-jump region, with the exact Lévy-measure integrability assumptions.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently authored Prove2Me draft pending exact-revision remote compiler verification. TimeSpacePoisson.lean lines 260–272.

import Mathlib.MeasureTheory.Function.L2Space
import Definitions.Def_levy_foundations_smallJumpIntegralLp
import Definitions.Def_levy_foundations_isCompensatedPoissonL2Extension

open MeasureTheory

theorem levy_foundations_smallJumpIntegralLpIsometry
    {Ω : Type} [MeasurableSpace Ω] (ν : Measure ℝ)
    [SigmaFinite ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → ℝ × ℝ)
    (I : Lp ℝ 2 (volume.prod ν) → Lp ℝ 2 μ)
    (hI : LevyFoundations.IsCompensatedPoissonL2Extension
      (volume.prod ν) μ K X I)
    (hν : LevyFoundations.isLevyMeasure ν) (t : ℝ) (ht : 0 ≤ t) :
    (eLpNorm (LevyFoundations.smallJumpIntegralLp ν μ I hν t) 2 μ) ^ 2 =
      ENNReal.ofReal t * ∫⁻ x in Set.Ioo (-1) 1,
        ENNReal.ofReal (x ^ 2) ∂ν := by sorry
