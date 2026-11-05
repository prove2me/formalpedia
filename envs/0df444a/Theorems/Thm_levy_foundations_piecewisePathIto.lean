-- Prove2me | Theorems.Thm_levy_foundations_piecewisePathIto
-- name    : levy_foundations_piecewisePathIto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:46:09.068916+00:00
-- url     : https://prove2.me/theorems/4160bf95-11de-48aa-a1ed-b26c640037b8
-- title:
--   Deterministic finite-jump change-of-variables formula
-- statement:
--   Deterministic finite-jump change-of-variables formula.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PiecewisePath.lean#L337

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

theorem levy_foundations_piecewisePathIto
    {x₀ b : ℝ} {T Y : ℕ → ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : Continuous f')
    (hmono : StrictMono T) (htop : Tendsto T atTop atTop)
    (hpos : 0 < T 0) {t : ℝ} (ht : 0 ≤ t) :
    f (LevyFoundations.piecewisePath x₀ b T Y t) -
      f (LevyFoundations.piecewisePath x₀ b T Y 0) =
      (∫ s in (0:ℝ)..t, f' (LevyFoundations.piecewisePath x₀ b T Y s) * b) +
      ∑ n ∈ Finset.range (LevyFoundations.jumpCount T t),
        (f (LevyFoundations.piecewisePath x₀ b T Y (T n)) -
        f (LevyFoundations.piecewisePath x₀ b T Y (T n) - Y n)) := by sorry
