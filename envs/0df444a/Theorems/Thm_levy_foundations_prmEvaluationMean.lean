-- Prove2me | Theorems.Thm_levy_foundations_prmEvaluationMean
-- name    : levy_foundations_prmEvaluationMean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:45:30.730148+00:00
-- url     : https://prove2.me/theorems/b59bf5a4-3807-4b78-a957-ca7916d21b75
-- title:
--   Unrestricted Poisson random-measure evaluation mean
-- statement:
--   For every measurable set A, including infinite-mass sets, the expected Poisson random-measure evaluation N(A) equals intensity m(A). Obtained from the finite-mass expectation bridge by an increasing sigma-finite exhaustion and the monotone convergence theorem. This is the exact core expectation lemma needed for Campbell's formula.
-- source:
--   Mathematically source-faithful to slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4; LeanLevy/RandomMeasure/PoissonRandomMeasure.lean original theorem lintegral_poissonRandomMeasure_apply lines 163–174, using alternative finite-mass plus monotone-limit route.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure

open MeasureTheory ProbabilityTheory Set

theorem levy_foundations_prmEvaluationMean
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {A : Set E} (hA : MeasurableSet A) :
    ∫⁻ ω, LevyFoundations.poissonRandomMeasure K X ω A ∂μ = m A := by sorry
