-- Prove2me | Definitions.Def_ReweightedNPMLE_FittedHessian
-- name    : ReweightedNPMLE_FittedHessian
-- status  : Definition
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:23:55.056903+00:00
-- url     : https://prove2.me/theorems/06aa44c6-b833-48a2-919b-89948785d0c3
-- title:
--   Linear and matrix forms of the fitted-log derivative
-- statement:
--   Identify a vector \(z\in\mathbb R^n\) with the continuous linear functional \(\Lambda_z(k)=\sum_i k_i z_i\); the map \(z\mapsto\Lambda_z\) is itself continuous and linear. Given a continuous linear operator \(J:\mathbb R^n\to\mathbb R^n\), define the associated bilinear form by
--   \[
--   B_J(h)(k)=\Lambda_{Jh}(k)=\sum_i k_i(Jh)_i.
--   \]
--   Also define its standard-coordinate matrix \(M(J)\) by \(M(J)_{ij}=(Je_j)_i\). When \(J\) is the derivative of the fitted log-vector, \(B_J\) represents the corresponding second derivative of the optimized likelihood value. Symmetry and positive semidefiniteness are subsequent conclusions under the relevant differentiability and optimality hypotheses.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedHessian.lean#L101-L353

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

namespace ReweightedNPMLE





noncomputable def fittedLogFunctionalMap (n : ℕ) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := fittedLogLinearFunctional
    map_add' := by
      intro z y
      ext h
      simp only [fittedLogLinearFunctional_apply, Pi.add_apply,
        ContinuousLinearMap.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    map_smul' := by
      intro r z
      ext h
      simp [fittedLogLinearFunctional_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring }



noncomputable def fittedSecondDerivativeOfLogDerivative {n : ℕ}
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ) :=
  (fittedLogFunctionalMap n).comp J















noncomputable def fittedLogDerivativeMatrix {n : ℕ}
    (J : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix' J.toLinearMap











end ReweightedNPMLE


