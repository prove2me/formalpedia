-- Prove2me | Theorems.Thm_levy_foundations_compoundPoissonPathwiseIto
-- name    : levy_foundations_compoundPoissonPathwiseIto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:47:34.12175+00:00
-- url     : https://prove2.me/theorems/50e01f40-3de1-4cf7-9bf7-337db33e7300
-- title:
--   Pathwise finite-activity Itô formula for compound Poisson with drift
-- statement:
--   Pathwise finite-activity Itô formula for compound Poisson with drift.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L354

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_levy_foundations_isCadlag
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Interval

theorem levy_foundations_compoundPoissonPathwiseIto
    {Ω : Type*} [MeasurableSpace Ω] {b : ℝ} {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0}
    {ν' : Measure ℝ} {μ : Measure Ω} (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f') :
    ∀ᵐ ω ∂μ, ∀ t : ℝ, 0 ≤ t →
      f (LevyFoundations.compoundPoisson b τ Y t ω) -
        f (LevyFoundations.compoundPoisson b τ Y 0 ω) =
      (∫ s in (0:ℝ)..t, f' (LevyFoundations.compoundPoisson b τ Y s ω) * b) +
      ∑ n ∈ Finset.range (LevyFoundations.jumpCount
          (fun m => LevyFoundations.arrival τ m ω) t),
        (f (LevyFoundations.compoundPoisson b τ Y (LevyFoundations.arrival τ n ω) ω) -
         f (LevyFoundations.compoundPoisson b τ Y (LevyFoundations.arrival τ n ω) ω - Y n ω)) := by sorry
