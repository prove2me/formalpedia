-- Prove2me | Theorems.Thm_ReweightedNPMLE_canonical_maximumIndependentSupport_gamma_moment
-- name    : ReweightedNPMLE.canonical_maximumIndependentSupport_gamma_moment
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:43:27.148261+00:00
-- url     : https://prove2.me/theorems/21678491-8a24-4cef-a005-1a04fa361f44
-- title:
--   Gamma determinant moment for the maximum independent support size
-- statement:
--   Let $n\ge1$, $\alpha>0$, and let $C\subset(0,\infty)^n$ be nonempty, compact, and convex. Let $D\subset C$ be closed, and let $\widehat v(w)$ maximize $\sum_iw_i\log v_i$ on $C$. For any fixed $z_0\in\mathbb R^n$, set $t(w)=\log\widehat v(w)-z_0$ on positive weights. Let $k(w)$ be the largest size of a linearly independent family in $D$ representing $\widehat v(w)$ with strictly positive coefficients summing to one, or zero if none exists. If $S\subset(0,\infty)^n$ is measurable and $\|t(w)\|_\infty\le1/8$ on $S$, then for independent $W_i\sim\operatorname{Gamma}(\alpha,\text{rate }\alpha)$,
--   $$
--   \mathbb E\!\left[\mathbf1_{\{W\in S\}}
--   \left(\frac{17}{9}\right)^{\max\{k(W)-1,0\}}
--   e^{-\alpha\{\sum_i(W_i-1)t_i(W)+\sum_it_i(W)^2\}}\right]\le1.
--   $$
--   The support statistic's measurability is derived; no measurable choice of representing atoms is assumed.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedDeterminantMoment.lean#L94-L156

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Canonical fitted-value determinant moment

The Gamma determinant moment is proved for a compact positive convex fitted
set and any measurable cardinality function realized by full-support extreme
finite representations.  The representing atoms and coefficients may vary
with the weights, and need not be measurable choices.  All analytic and
change-of-variables hypotheses follow from canonical fitted-value regularity
and support sensitivity.
-/

open Set Filter MeasureTheory
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.canonical_maximumIndependentSupport_gamma_moment
    {n : ℕ} [Nonempty (Fin n)] {α : ℝ} (hα : 0 < α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (z₀ : Fin n → ℝ)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) (hspos : s ⊆ positiveVectors n)
    (ht : ∀ w ∈ s, ∀ i,
      |fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i| ≤ 1 / 8) :
    let t := fittedLogDisplacement C hCcompact hCnonempty hCpos z₀
    let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
    ∫⁻ w in s, ENNReal.ofReal
        ((17 / 9 : ℝ) ^ (k w - 1) * Real.exp (-α *
          (∑ i, (w i - 1) * t w i + ∑ i, (t w i) ^ 2)))
      ∂gammaProductMeasure n α α ≤ 1 := by sorry
