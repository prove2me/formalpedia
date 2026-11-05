-- Prove2me | Theorems.Thm_levy_foundations_prmEvaluationMeanFinite
-- name    : levy_foundations_prmEvaluationMeanFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:27:47.4062+00:00
-- url     : https://prove2.me/theorems/feedcd17-fef9-47d4-9f20-173508c10a70
-- title:
--   Finite-mass Poisson random-measure evaluation has correct mean
-- statement:
--   For a measurable set A of finite intensity, the expectation of the Poisson random-measure count N(A) equals m(A). This is the finite-mass bridge between the proved Poisson count law and LeanLevy's general Campbell formula.
-- source:
--   Derived source-faithfully from slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonRandomMeasure.lean lines 133–172, with proved mission count law and measurable evaluation.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure

open MeasureTheory ProbabilityTheory

theorem levy_foundations_prmEvaluationMeanFinite
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {A : Set E} (hA : MeasurableSet A) (hfin : m A < ⊤) :
    ∫⁻ ω, LevyFoundations.poissonRandomMeasure K X ω A ∂μ = m A := by sorry
