-- Prove2me | Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
-- name    : ReweightedNPMLE_GammaEffectiveEvent
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:23:48.006121+00:00
-- url     : https://prove2.me/theorems/da199ca5-78a0-4b09-bbe0-e27e6933db49
-- title:
--   The common Gamma concentration event
-- statement:
--   For integers \(n,r\), real parameters \(\alpha,q\), and a Euclidean subspace \(V\subseteq\mathbb R^n\), set
--   \[
--   Q_n(q)=q+\log(2n),\qquad N_r(q)=r\log5+q.
--   \]
--   The common concentration event consists of weight vectors satisfying both
--   \[
--   \max_i|w_i-1|\le2\sqrt{Q_n(q)/\alpha}
--   \quad\text{and}\quad
--   \sqrt\alpha\,\|P_V(w-\mathbf1)\|_2
--   \le4\sqrt{N_r(q)},
--   \]
--   where \(P_V\) is the orthogonal projection onto \(V\). The first condition is expressed coordinatewise, so it also has an unambiguous empty-coordinate interpretation. The event simultaneously controls the largest coordinate fluctuation and the fluctuation projected into the approximation space. Gamma concentration results impose the positive-shape and dimension hypotheses separately.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaEffectiveEvent.lean#L19-L28

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

namespace ReweightedNPMLE

noncomputable def effectiveQ (n : ℕ) (q : ℝ) : ℝ := q + Real.log (2 * (n : ℝ))

noncomputable def effectiveN (r : ℕ) (q : ℝ) : ℝ := (r : ℝ) * Real.log 5 + q

noncomputable def gammaEffectiveEvent {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (r : ℕ) (α q : ℝ) :
    Set (Fin n → ℝ) :=
  {w | (∀ i, |w i - 1| ≤ 2 * Real.sqrt (effectiveQ n q / α)) ∧
    Real.sqrt α * ‖V.starProjection (WithLp.toLp 2 (fun i ↦ w i - 1))‖ ≤
      4 * Real.sqrt (effectiveN r q)}







end ReweightedNPMLE


