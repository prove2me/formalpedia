-- Prove2me | Theorems.Thm_levy_foundations_prmIndependent
-- name    : levy_foundations_prmIndependent
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T15:16:56.849546+00:00
-- url     : https://prove2.me/theorems/5b8516f5-d9f1-461c-af8b-e81610a6d07a
-- title:
--   Independent scattering for disjoint finite-intensity sets
-- statement:
--   Evaluations on two disjoint measurable sets of finite intensity are independent under the probability measure carrying the Poisson point family.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L741-L752. Two-set independently scattered property. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_poissonRandomMeasure

open MeasureTheory ProbabilityTheory

theorem levy_foundations_prmIndependent
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤)
    (hAB : Disjoint A B) :
    IndepFun
      (fun ω => LevyFoundations.poissonRandomMeasure K X ω A)
      (fun ω => LevyFoundations.poissonRandomMeasure K X ω B) μ := by sorry
