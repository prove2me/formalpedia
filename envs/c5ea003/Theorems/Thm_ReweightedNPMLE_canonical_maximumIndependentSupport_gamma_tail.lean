-- Prove2me | Theorems.Thm_ReweightedNPMLE_canonical_maximumIndependentSupport_gamma_tail
-- name    : ReweightedNPMLE.canonical_maximumIndependentSupport_gamma_tail
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:44:28.063799+00:00
-- url     : https://prove2.me/theorems/f7411cb6-018a-45d0-bcf0-01ba01e1e5bd
-- title:
--   Exponential tail bound for the maximum independent fitted support
-- statement:
--   Let $n\ge1$, $\alpha>0$, and let $C\subset(0,\infty)^n$ be nonempty, compact, and convex. Let $D\subset C$ be closed and let $\widehat v(w)$ maximize $\sum_iw_i\log v_i$ over $C$. Define $k(w)$ as the largest size of a linearly independent list from $D$ whose strictly positive convex combination equals $\widehat v(w)$, with value zero if no such representation exists. Fix $z_0\in\mathbb R^n$ and put $t(w)=\log\widehat v(w)-z_0$ for positive $w$. On a measurable $S\subset(0,\infty)^n$, assume $|t_i(w)|\le1/8$ and $\alpha\{\langle w-\mathbf1,t(w)\rangle+\|t(w)\|_2^2\}\le H$. For any real $H,q$ and iid $W_i\sim\operatorname{Gamma}(\alpha,\text{rate }\alpha)$,
--   $$
--   \mathbb P\!\left(W\in S,\ H+q\le\log(17/9)\max\{k(W)-1,0\}\right)\le e^{-q}.
--   $$
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/EffectiveDimension.lean#L115-L163

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
import Mathlib.Analysis.SpecialFunctions.Exponential
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Real
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
# Probability assembly for effective-dimension sparsification

This file formalizes the Markov and event-union steps used after the radial
localization and determinant-moment estimates in Theorem 3.1.
-/

open MeasureTheory Set

open ReweightedNPMLE

theorem ReweightedNPMLE.canonical_maximumIndependentSupport_gamma_tail
    {n : ℕ} [Nonempty (Fin n)] {α : ℝ} (hα : 0 < α)
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C)
    (hCcompact : IsCompact C) (hCnonempty : C.Nonempty)
    (hCpos : C ⊆ positiveVectors n)
    (D : Set (Fin n → ℝ)) (hDclosed : IsClosed D) (hD : D ⊆ C)
    (z₀ : Fin n → ℝ)
    {s : Set (Fin n → ℝ)} (hs : MeasurableSet s) (hspos : s ⊆ positiveVectors n)
    (ht : ∀ w ∈ s, ∀ i,
      |fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i| ≤ 1 / 8)
    (H q : ℝ)
    (hcost : ∀ w ∈ s,
      α * (∑ i, (w i - 1) * fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i +
        ∑ i, (fittedLogDisplacement C hCcompact hCnonempty hCpos z₀ w i) ^ 2) ≤ H) :
    let k := maximumIndependentSupport D (fittedValueSelection C hCcompact hCnonempty hCpos)
    (gammaProductMeasure n α α).real {w | w ∈ s ∧
      H + q ≤ Real.log (17 / 9 : ℝ) * ((k w - 1 : ℕ) : ℝ)} ≤ Real.exp (-q) := by sorry
