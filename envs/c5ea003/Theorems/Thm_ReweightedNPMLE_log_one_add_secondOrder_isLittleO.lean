-- Prove2me | Theorems.Thm_ReweightedNPMLE_log_one_add_secondOrder_isLittleO
-- name    : ReweightedNPMLE.log_one_add_secondOrder_isLittleO
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:20.22989+00:00
-- url     : https://prove2.me/theorems/6898c530-a911-4a9f-a6bc-60f17314b92f
-- title:
--   Second-order logarithm expansion along positive perturbations
-- statement:
--   For each fixed $q\in\mathbb R$, the logarithm admits the expansion
--   $$
--   \log(1+tq)=tq-\frac{t^2q^2}{2}+o(t^2)
--   \qquad\text{as }t\downarrow0.
--   $$
--   Equivalently, the difference between the logarithm and the displayed quadratic polynomial, divided by $t^2$, tends to zero through positive values of $t$. No sign restriction on $q$ is imposed; $1+tq$ is positive for all sufficiently small positive $t$.
--
--   The one-sided remainder form is suited to feasible directions that preserve nonnegative mixture coefficients and supplies the scalar expansion used in support-sensitivity arguments.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedHessian.lean#L76-L99

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

theorem ReweightedNPMLE.log_one_add_secondOrder_isLittleO (q : ℝ) :
    (fun t : ℝ ↦ Real.log (1 + t * q) - t * q +
        (t ^ 2 / 2) * q ^ 2) =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by sorry
