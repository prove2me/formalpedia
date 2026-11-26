-- Prove2me | Theorems.Thm_ReweightedNPMLE_exists_submodule_directional_net
-- name    : ReweightedNPMLE.exists_submodule_directional_net
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:46:18.324406+00:00
-- url     : https://prove2.me/theorems/ce0f03f2-56d2-5bf9-9025-e1dc284045af
-- title:
--   Directional net for a Euclidean subspace of bounded rank
-- statement:
--   Let $V\subset\mathbb R^n$ have dimension at most $r$. There is a finite set $N\subset\mathbb R^n$ with $|N|\le5^r$ and $\|v\|_2\le1$ for $v\in N$, such that $$\forall y\in V\ \exists v\in N\cap V:\ \|y\|_2\le2\langle v,y\rangle.$$ The result includes the zero subspace. It supplies the finite net required for projected Gamma concentration.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaProjection.lean#L507-L554

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

theorem ReweightedNPMLE.exists_submodule_directional_net {n r : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hrank : Module.finrank ℝ V ≤ r) :
    ∃ N : Finset (EuclideanSpace ℝ (Fin n)),
      N.card ≤ 5 ^ r ∧
      (∀ v ∈ N, ∑ i, (v i) ^ 2 ≤ 1) ∧
      ∀ y ∈ V, ∃ v ∈ N, v ∈ V ∧ ‖y‖ ≤ 2 * inner ℝ v y := by sorry
