-- Prove2me | Theorems.Thm_levy_foundations_totalCountVecCharFun
-- name    : levy_foundations_totalCountVecCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:03:57.458594+00:00
-- url     : https://prove2.me/theorems/e15ea110-1658-42bb-bbf0-b03a48f6544f
-- title:
--   Joint characteristic function of full Poisson random-measure count vectors
-- statement:
--   Pass from the partial count vectors to the full finite-intensity Poisson count vector by dominated convergence of bounded complex exponentials, and convergence of truncated intensity sums.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonRandomMeasure.lean, charFunDual_poissonRandomMeasureVec around line 870.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Definitions.Def_levy_foundations_poissonRandomMeasure

open MeasureTheory ProbabilityTheory Complex

theorem levy_foundations_totalCountVecCharFun
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι] [DecidableEq ι]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hfin : ∀ i, m (A i) < ⊤)
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) =>
      (LevyFoundations.poissonRandomMeasure K X ω (A i)).toReal) L =
    ∏ i, Complex.exp
      (↑(m (A i)).toReal *
        (Complex.exp (↑(L (Pi.single i 1)) * Complex.I) - 1)) := by sorry
