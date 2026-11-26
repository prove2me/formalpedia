-- Prove2me | Theorems.Thm_ReweightedNPMLE_fittedLogDerivative_quadratic_nonneg
-- name    : ReweightedNPMLE.fittedLogDerivative_quadratic_nonneg
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:40:07.908723+00:00
-- url     : https://prove2.me/theorems/f831536a-1c08-4dbb-86b4-9b8ca9b7198b
-- title:
--   Nonnegative quadratic form of the fitted-log derivative
-- statement:
--   Let $n\ge1$, let $C\subset\mathbb R^n$, and suppose $\widehat v(u)$ maximizes $\sum_i u_i\ell(v_i)$ over $C$ for every real weight vector $u$. Here $\ell(x)=\log|x|$ for nonzero $x$ and $\ell(0)=0$. Define $z(u)_i=\ell(\widehat v(u)_i)$. If $z$ is Fréchet differentiable at $w$ with derivative $J$, then
--   $$
--   \sum_{i=1}^n h_i(Jh)_i\ge0
--   \qquad\text{for every }h\in\mathbb R^n.
--   $$
--   No separate convexity assumption on $C$ is imposed.
--
--   This establishes the nonnegative quadratic-form component of the positive-semidefinite Hessian structure associated with the optimized weighted objective.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedHessian.lean#L288-L349

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Hessian structure of the fitted likelihood value

This file turns the envelope identity into the analytic Hessian facts used by
the paper.  The derivative of the fitted log-vector induces the second
derivative of the optimized value.  Mathlib's second-derivative symmetry
theorem makes its matrix Hermitian, while monotonicity of fitted logs makes
its quadratic form nonnegative.  Thus, at every differentiability point, the
matrix representing the fitted-log derivative is positive semidefinite.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.fittedLogDerivative_quadratic_nonneg {n : ℕ} [Nonempty (Fin n)]
    {C : Set (Fin n → ℝ)}
    (vhat : (Fin n → ℝ) → (Fin n → ℝ))
    (hmax : ∀ u, IsMaxOn C (weightedLogLikelihood u) (vhat u))
    {w : Fin n → ℝ} {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt (fun u i ↦ Real.log (vhat u i)) J w)
    (h : Fin n → ℝ) :
    0 ≤ ∑ i, h i * J h i := by sorry
