-- Prove2me | Theorems.Thm_ReweightedNPMLE_half_separated_sphere_card_le_five_pow
-- name    : ReweightedNPMLE.half_separated_sphere_card_le_five_pow
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:44:56.793319+00:00
-- url     : https://prove2.me/theorems/c3707f59-212c-4a32-86df-d76692435916
-- title:
--   Packing bound for a half-separated Euclidean unit sphere
-- statement:
--   Let $E$ be a nontrivial finite-dimensional real inner-product space of dimension $d$, with its Borel measurable structure. If a finite set $C\subset E$ consists of unit vectors and distinct points have distance strictly greater than $1/2$, then $$|C|\le5^d.$$ This is the geometric cardinality bound for the directional concentration net.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaProjection.lean#L361-L411

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

theorem ReweightedNPMLE.half_separated_sphere_card_le_five_pow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (C : Finset E)
    (hSphere : ∀ x ∈ C, ‖x‖ = 1)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → (1 / 2 : ℝ) < dist x y) :
    C.card ≤ 5 ^ Module.finrank ℝ E := by sorry
