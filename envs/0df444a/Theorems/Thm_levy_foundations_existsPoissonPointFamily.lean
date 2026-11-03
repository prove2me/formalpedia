-- Prove2me | Theorems.Thm_levy_foundations_existsPoissonPointFamily
-- name    : levy_foundations_existsPoissonPointFamily
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:30:47.227315+00:00
-- url     : https://prove2.me/theorems/2db13314-b41a-4c01-85e7-113a12d7d163
-- title:
--   Existence of a Poisson point family for a sigma-finite intensity
-- statement:
--   For every sigma-finite intensity measure on a nonempty measurable space, construct a probability space carrying independent Poisson piece counts and independent marks with their prescribed normalised laws.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L249-L270. Existence via independent product probability space. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_pointFamilyLaw
import Theorems.Thm_levy_foundations_prmPieceLawProb

open MeasureTheory ProbabilityTheory

theorem levy_foundations_existsPoissonPointFamily
    {E : Type} [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E),
      IsProbabilityMeasure μ ∧
        LevyFoundations.IsPoissonPointFamily K X m μ := by sorry
