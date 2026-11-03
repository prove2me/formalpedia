-- Prove2me | Theorems.Thm_levy_foundations_poissonTimeCountIndependentBands
-- name    : levy_foundations_poissonTimeCountIndependentBands
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T15:19:05.920989+00:00
-- url     : https://prove2.me/theorems/0897b621-3ca4-4d94-930b-01f84e7f0267
-- title:
--   Independent increments of time-space Poisson counts
-- statement:
--   Count variables on successive disjoint time bands are mutually independent for ordered time cut-offs.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L156-L165. Independently authored Prove2Me draft, awaiting remote compilation.

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Process.Basic
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Definitions.Def_levy_foundations_isPoissonPointFamily

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem levy_foundations_poissonTimeCountIndependentBands
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E] [Nonempty E]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (K : ℕ → Ω → ℕ)
    (X : ℕ → ℕ → Ω → ℝ × E) (A : Set E)
    (hd : LevyFoundations.IsPoissonPointFamily K X (volume.prod m) μ)
    (hA : MeasurableSet A) (hfin : m A < ⊤)
    {n : ℕ} {t : Fin (n + 1) → ℝ} (ht : Monotone t) :
    iIndepFun (fun (i : Fin n) ω =>
      LevyFoundations.poissonRandomMeasure K X ω
        (Set.Ioc (t i.castSucc) (t i.succ) ×ˢ A)) μ := by sorry
