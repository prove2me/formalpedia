-- Prove2me | Theorems.Thm_levy_foundations_thinnedCountVecCharFun
-- name    : levy_foundations_thinnedCountVecCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:26:17.098067+00:00
-- url     : https://prove2.me/theorems/06ee9f69-4823-456a-bc52-b06ab816ff2c
-- title:
--   Joint characteristic-function factorisation within one marked Poisson piece
-- statement:
--   Within any finite-intensity piece, the characteristic function of the vector of counts on pairwise-disjoint sets factors into Poisson characteristic functions. This establishes the base case for finite-piece superposition.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean, charFunDual_pi_thinnedCount at line 1394.

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Definitions.Def_levy_foundations_thinnedCount
import Theorems.Thm_levy_foundations_thinnedCountMeasurable
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_prmPiece
import Theorems.Thm_levy_foundations_poissonPieceProdPGF
import Theorems.Thm_levy_foundations_prmPieceLawMassBridge
import Theorems.Thm_levy_foundations_jointPGFOnePiece
import Theorems.Thm_levy_foundations_piDualApply

open MeasureTheory ProbabilityTheory Complex

theorem levy_foundations_thinnedCountVecCharFun
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι] [DecidableEq ι]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (k : ℕ) (L : StrongDual ℝ (ι → ℝ)) :
    charFunDual (μ.map fun ω (i : ι) =>
      (LevyFoundations.thinnedCount K X (A i) k ω : ℝ)) L =
    ∏ i, Complex.exp ((m (LevyFoundations.prmPiece m k ∩ A i)).toReal *
      (Complex.exp (↑(L (Pi.single i 1)) * Complex.I) - 1)) := by sorry
