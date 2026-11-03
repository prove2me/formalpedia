-- Prove2me | Theorems.Thm_levy_foundations_partialCountVecCharFun
-- name    : levy_foundations_partialCountVecCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:34:21.814504+00:00
-- url     : https://prove2.me/theorems/fbb02ba6-de83-457d-b5f6-9add895697b5
-- title:
--   Joint characteristic function of finitely superposed Poisson count vectors
-- statement:
--   By induction across independent pieces, the joint characteristic function of the count vector from pieces 0 through n is the product of Poisson factors with the accumulated truncated intensity per coordinate.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonRandomMeasure.lean, charFunDual_prmPartialCountVec around line 830.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_prmPartialCount
import Definitions.Def_levy_foundations_prmPiece
import Theorems.Thm_levy_foundations_thinnedCountVecCharFun
import Theorems.Thm_levy_foundations_partialNextVecIndependent
import Theorems.Thm_levy_foundations_prmPartialCountSucc
import Theorems.Thm_levy_foundations_prmPartialCountMeasurable
import Theorems.Thm_levy_foundations_thinnedCountMeasurable

open MeasureTheory ProbabilityTheory Complex

theorem levy_foundations_partialCountVecCharFun
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι] [DecidableEq ι]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (n : ℕ) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) =>
      (LevyFoundations.prmPartialCount K X (A i) n ω : ℝ)) L =
    ∏ i, Complex.exp
      (↑(∑ k ∈ Finset.range (n + 1),
        (m (LevyFoundations.prmPiece m k ∩ A i)).toReal) *
        (Complex.exp (↑(L (Pi.single i 1)) * Complex.I) - 1)) := by sorry
