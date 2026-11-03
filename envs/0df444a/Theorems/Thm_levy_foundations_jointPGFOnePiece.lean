-- Prove2me | Theorems.Thm_levy_foundations_jointPGFOnePiece
-- name    : levy_foundations_jointPGFOnePiece
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:13:14.193441+00:00
-- url     : https://prove2.me/theorems/2799adcb-0052-4386-837e-3f199e087241
-- title:
--   Joint Poisson generating function for disjoint marked sets within one piece
-- statement:
--   For finitely many pairwise-disjoint measurable sets inside a Poisson partition piece, the joint generating function of the associated thinned counts factorises as a finite product of Poisson generating functions, including zero-intensity pieces.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), PoissonPointFamily.lean, frozen source commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Awaiting private remote Lean verification. Based on integral_prod_pow_thinnedCount.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Probability.Independence.Integration
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_thinnedCount
import Theorems.Thm_levy_foundations_prodIteConstCard
import Theorems.Thm_levy_foundations_prodIteDisjoint
import Theorems.Thm_levy_foundations_poissonPieceProdPGF
import Theorems.Thm_levy_foundations_prmPieceLawMassBridge

open MeasureTheory ProbabilityTheory Complex

theorem levy_foundations_jointPGFOnePiece
    {Ω E : Type} {ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] [Fintype ι]
    (m : Measure E) [SigmaFinite m] (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : ι → Set E) (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (k : ℕ) (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∫ ω, ∏ i, (z i) ^ (LevyFoundations.thinnedCount K X (A i) k ω) ∂μ =
      ∏ i, Complex.exp ((m (LevyFoundations.prmPiece m k ∩ A i)).toReal * (z i - 1)) := by sorry
