-- Prove2me | Theorems.Thm_levy_foundations_prmCampbell
-- name    : levy_foundations_prmCampbell
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T15:17:09.656095+00:00
-- url     : https://prove2.me/theorems/abcfc254-3a21-462b-b0a1-b535fe67a34f
-- title:
--   Campbell formula for nonnegative integrands
-- statement:
--   The expected integral of any measurable nonnegative function g against the Poisson random measure equals its integral against the deterministic intensity m. Both sides may be infinite.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L1010-L1020. Campbell's formula with nonnegative integrands. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory ProbabilityTheory

theorem levy_foundations_prmCampbell
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {g : E → ENNReal} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ x, g x ∂(LevyFoundations.poissonRandomMeasure K X ω) ∂μ
      = ∫⁻ x, g x ∂m := by sorry
