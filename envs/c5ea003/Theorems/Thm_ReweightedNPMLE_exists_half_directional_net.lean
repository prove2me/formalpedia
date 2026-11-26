-- Prove2me | Theorems.Thm_ReweightedNPMLE_exists_half_directional_net
-- name    : ReweightedNPMLE.exists_half_directional_net
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:45:58.181203+00:00
-- url     : https://prove2.me/theorems/8b8480ad-9eff-4f94-96bb-90c91deeaf57
-- title:
--   A finite net controlling every norm by a directional inner product
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real inner-product space of dimension $d$, equipped with its Borel measurable structure. There exists a finite set $N$ of unit vectors with $$|N|\le5^d,\qquad\forall y\in E\ \exists v\in N:\ \|y\|\le2\langle v,y\rangle.$$ This form of a sphere net is suited to one-sided tail estimates.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaProjection.lean#L464-L505

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

open ReweightedNPMLE

















/-! ### A Euclidean half-net with the paper's `5 ^ r` cardinality bound -/

theorem ReweightedNPMLE.exists_half_directional_net
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E] :
    ∃ N : Finset E,
      N.card ≤ 5 ^ Module.finrank ℝ E ∧
      (∀ v ∈ N, ‖v‖ = 1) ∧
      ∀ y : E, ∃ v ∈ N, ‖y‖ ≤ 2 * inner ℝ v y := by sorry
