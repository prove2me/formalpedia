-- Prove2me | Theorems.Thm_ReweightedNPMLE_weightedLogLikelihood_multiplicative_secondOrder
-- name    : ReweightedNPMLE.weightedLogLikelihood_multiplicative_secondOrder
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:46.193032+00:00
-- url     : https://prove2.me/theorems/1ab6226f-d359-5e45-88d4-ca0ce0ce1013
-- title:
--   Second-order expansion along coupled weight and fitted-value paths
-- statement:
--   Write $L_w(v)=\sum_iw_i\log v_i$. For arbitrary $w,h,u\in\mathbb R^n$ and coordinatewise positive $v$, as $t\downarrow0$, $$L_{w+th}(v\odot(1+tu))=L_w(v)+t\left(\sum_i h_i\log v_i+\sum_iw_iu_i\right)+t^2\left(\sum_i h_iu_i-\tfrac12\sum_iw_iu_i^2\right)+o(t^2).$$ Positivity of $w$ is not required. This is the candidate-path expansion used in the support-sensitivity comparison.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivityAnalytic.lean#L21-L85

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
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Analytic support sensitivity

This file supplies the scalar second-order likelihood expansion behind the
paper's support--sensitivity inequality.  It combines the Taylor expansion of
`log (1 + t u)` with simultaneous perturbations of the observation weights.
-/

open Set Filter Asymptotics
open Matrix
open scoped BigOperators Topology

open ReweightedNPMLE

theorem ReweightedNPMLE.weightedLogLikelihood_multiplicative_secondOrder {n : ℕ}
    (w h v u : Fin n → ℝ) (hv : ∀ i, 0 < v i) :
    (fun t : ℝ ↦
      weightedLogLikelihood (w + t • h) (fun i ↦ v i * (1 + t * u i)) -
        weightedLogLikelihood w v -
        t * ((∑ i, h i * Real.log (v i)) + ∑ i, w i * u i) -
        t ^ 2 * ((∑ i, h i * u i) - (1 / 2 : ℝ) * ∑ i, w i * u i ^ 2))
      =o[nhdsWithin 0 (Ioi 0)] (fun t : ℝ ↦ t ^ 2) := by sorry
