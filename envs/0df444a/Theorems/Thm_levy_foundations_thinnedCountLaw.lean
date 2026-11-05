-- Prove2me | Theorems.Thm_levy_foundations_thinnedCountLaw
-- name    : levy_foundations_thinnedCountLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T17:13:32.281368+00:00
-- url     : https://prove2.me/theorems/03c12fc9-8386-46a8-874d-8a8c92258c6c
-- title:
--   Poisson thinning law for a single intensity piece
-- statement:
--   The number of marked points of the kth Poisson piece landing in A follows a Poisson law with rate m(piece(k)∩A).
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), frozen source commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/RandomMeasure/PoissonPointFamily.lean, map_thinnedCount at line 1195.

import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_thinnedCount
import Definitions.Def_levy_foundations_isPoissonPointFamily
import Definitions.Def_levy_foundations_prmPiece

open MeasureTheory ProbabilityTheory

theorem levy_foundations_thinnedCountLaw
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [Nonempty E] (m : Measure E) [SigmaFinite m]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (hd : LevyFoundations.IsPoissonPointFamily K X m μ)
    (A : Set E) (hA : MeasurableSet A) (k : ℕ) :
    μ.map (LevyFoundations.thinnedCount K X A k) =
      poissonMeasure (m (LevyFoundations.prmPiece m k ∩ A)).toNNReal := by sorry
