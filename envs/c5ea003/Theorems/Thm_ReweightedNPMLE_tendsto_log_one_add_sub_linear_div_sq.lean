-- Prove2me | Theorems.Thm_ReweightedNPMLE_tendsto_log_one_add_sub_linear_div_sq
-- name    : ReweightedNPMLE.tendsto_log_one_add_sub_linear_div_sq
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:38:47.117009+00:00
-- url     : https://prove2.me/theorems/d6d400ac-8282-568d-8e88-5d5e47115323
-- title:
--   Quadratic limit of the logarithmic linearization remainder
-- statement:
--   For every real number $q$, the logarithmic remainder has the punctured two-sided limit
--   $$
--   \lim_{\substack{t\to0\\t\ne0}}
--   \frac{\log(1+tq)-tq}{t^2}=-\frac{q^2}{2}.
--   $$
--   The parameter $q$ is fixed but otherwise unrestricted, including $q=0$. For all sufficiently small $t$, the argument $1+tq$ is positive, so the expression agrees with the ordinary real logarithm.
--
--   This scalar limit identifies the exact quadratic coefficient in the local logarithmic expansion. It is used when comparing likelihood along feasible perturbations and when extracting second-order curvature information from fitted-value optimality.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FittedHessian.lean#L26-L74

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

theorem ReweightedNPMLE.tendsto_log_one_add_sub_linear_div_sq (q : ℝ) :
    Tendsto (fun t : ℝ ↦ (Real.log (1 + t * q) - t * q) / t ^ 2)
      (nhdsWithin 0 {0}ᶜ) (nhds (-(q ^ 2) / 2)) := by sorry
