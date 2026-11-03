-- Prove2me | Theorems.Thm_levy_foundations_piecewisePathIsCadlag
-- name    : levy_foundations_piecewisePathIsCadlag
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:45:52.089007+00:00
-- url     : https://prove2.me/theorems/e3f77d65-eeb6-4b63-b035-d78f97e9b696
-- title:
--   Piecewise-affine jump paths are càdlàg
-- statement:
--   Piecewise-affine jump paths are càdlàg.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PiecewisePath.lean#L226

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

theorem levy_foundations_piecewisePathIsCadlag
    {x₀ b : ℝ} {T Y : ℕ → ℝ} (hmono : StrictMono T) (htop : Tendsto T atTop atTop) :
    LevyFoundations.isCadlag (LevyFoundations.piecewisePath x₀ b T Y) := by sorry
