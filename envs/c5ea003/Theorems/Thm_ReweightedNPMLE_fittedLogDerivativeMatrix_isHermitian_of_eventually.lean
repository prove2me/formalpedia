-- Prove2me | Theorems.Thm_ReweightedNPMLE_fittedLogDerivativeMatrix_isHermitian_of_eventually
-- name    : ReweightedNPMLE.fittedLogDerivativeMatrix_isHermitian_of_eventually
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:13.420443+00:00
-- url     : https://prove2.me/theorems/2e1bc229-e0a4-4815-8081-1192d6f27595
-- title:
--   Symmetry of a derivative matrix arising from a local gradient field
-- statement:
--   Let $\psi:\mathbb R^n\to\mathbb R$ and $z:\mathbb R^n\to\mathbb R^n$. Assume that, in a neighborhood of $w$, $\psi$ is Fréchet differentiable with $D\psi(u)[h]=\sum_i h_i z(u)_i$. If $z$ is Fréchet differentiable at $w$ with derivative $J$, its standard-coordinate matrix $M$, defined by $M_{ij}=(Je_j)_i$, satisfies
--   $$
--   M_{ij}=M_{ji}\qquad\text{for all }i,j.
--   $$
--   Thus the real matrix is Hermitian, equivalently symmetric.
--
--   The conclusion requires the gradient identity only locally and does not assume that $z$ is continuously differentiable throughout a neighborhood.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedHessian.lean#L386-L412

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

theorem ReweightedNPMLE.fittedLogDerivativeMatrix_isHermitian_of_eventually {n : ℕ}
    (psi : (Fin n → ℝ) → ℝ)
    (z : (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin n → ℝ}
    (hpsi : ∀ᶠ u in 𝓝 w,
      HasFDerivAt psi (fittedLogLinearFunctional (z u)) u)
    {J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)}
    (hz : HasFDerivAt z J w) :
    (fittedLogDerivativeMatrix J).IsHermitian := by sorry
