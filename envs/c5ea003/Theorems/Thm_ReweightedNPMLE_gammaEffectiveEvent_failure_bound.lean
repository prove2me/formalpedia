-- Prove2me | Theorems.Thm_ReweightedNPMLE_gammaEffectiveEvent_failure_bound
-- name    : ReweightedNPMLE.gammaEffectiveEvent_failure_bound
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:47:13.678798+00:00
-- url     : https://prove2.me/theorems/89378aed-b802-4060-b0c8-9b35dbdfbc4f
-- title:
--   Joint coordinate and projected-energy Gamma event
-- statement:
--   Let $n\ge1$, $q\ge1$, $\alpha>0$, and let $V\subset\mathbb R^n$ have dimension at most $r$. Put $Q=q+\log(2n)$ and $N=r\log5+q$, and suppose $4Q,4N\le\alpha$. For independent $W_i\sim\operatorname{Gamma}(\alpha,\alpha)$, define $$E=\{\|W-\mathbf1\|_\infty\le2\sqrt{Q/\alpha},\quad\sqrt\alpha\|P_V(W-\mathbf1)\|_2\le4\sqrt N\}.$$ Then $\Pr(E^c)\le2e^{-q}$. This combines coordinate control and effective-dimensional energy control in one event.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaEffectiveEvent.lean#L44-L101

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Common Gamma concentration and localization event

The projected-energy and maximum-coordinate bounds hold jointly with
failure probability at most `2 exp(-q)`.  Explicit scale conditions imply
all radial localization hypotheses and the sharp `alpha E <= 2` width
cost bound.
-/

open Set Filter MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.gammaEffectiveEvent_failure_bound {n r : ℕ} [Nonempty (Fin n)]
    {α q : ℝ} (hα : 0 < α) (hq : 1 ≤ q)
    (hαQ : 4 * effectiveQ n q ≤ α) (hαN : 4 * effectiveN r q ≤ α)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hrank : Module.finrank ℝ V ≤ r) :
    (gammaProductMeasure n α α).real (gammaEffectiveEvent V r α q)ᶜ ≤ 2 * Real.exp (-q) := by sorry
