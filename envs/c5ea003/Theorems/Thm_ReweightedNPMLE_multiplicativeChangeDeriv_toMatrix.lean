-- Prove2me | Theorems.Thm_ReweightedNPMLE_multiplicativeChangeDeriv_toMatrix
-- name    : ReweightedNPMLE.multiplicativeChangeDeriv_toMatrix
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:38.562098+00:00
-- url     : https://prove2.me/theorems/638a60e5-5d17-45c9-8b28-d04a0aabc6ea
-- title:
--   Matrix of the derivative of a coordinatewise multiplicative map
-- statement:
--   Let $w,u\in\mathbb R^n$, and let $L:\mathbb R^n\to\mathbb R^n$ be a continuous linear map with standard-basis matrix $M$. Define the linear map
--   $$T(h)=w\odot L(h)+(1+u)\odot h,$$
--   where $\odot$ denotes coordinatewise multiplication. Its standard-basis matrix is
--   $$[T]=\operatorname{diag}(1+u)+\operatorname{diag}(w)M.$$
--   Equivalently, $[T]_{ij}=(1+u_i)\delta_{ij}+w_iM_{ij}$. With $u=t(w)$ and $L=Dt(w)$, this is the Jacobian matrix of $F(w)=w\odot(1+t(w))$. The identity itself is purely linear algebra and requires no differentiability hypothesis.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/ChangeOfVariables.lean#L190-L213

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Injective change of variables for determinant moments

This file packages the precise area-formula step used by the paper's
determinant-moment argument.  If an injective differentiable map sends a
localized event into a probability density, its density-weighted Jacobian
has integral at most one.  A pointwise Jacobian/density comparison then
transfers that bound to the desired random variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.multiplicativeChangeDeriv_toMatrix
    {n : ℕ} (w u : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    LinearMap.toMatrix' (w • L + (1 + u) •
      ContinuousLinearMap.id ℝ (Fin n → ℝ)).toLinearMap =
      Matrix.diagonal (fun i ↦ 1 + u i) +
        Matrix.diagonal w * LinearMap.toMatrix' L.toLinearMap := by sorry
