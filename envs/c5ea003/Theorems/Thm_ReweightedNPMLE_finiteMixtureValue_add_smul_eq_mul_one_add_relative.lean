-- Prove2me | Theorems.Thm_ReweightedNPMLE_finiteMixtureValue_add_smul_eq_mul_one_add_relative
-- name    : ReweightedNPMLE.finiteMixtureValue_add_smul_eq_mul_one_add_relative
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:06.593571+00:00
-- url     : https://prove2.me/theorems/77ec6d9b-a753-4050-b016-4253d2b80b40
-- title:
--   Affine coefficient changes produce multiplicative relative fitted paths
-- statement:
--   Let $A_1,\ldots,A_k\in\mathbb R^n$ and $p\in\mathbb R^k$ satisfy $\sum_jp_jA_j=v$, with every $v_i\ne0$. For arbitrary $c\in\mathbb R^k$ and $t\in\mathbb R$, put $u_i=\sum_jc_jA_{ji}/v_i$. Then $$\sum_j(p_j+tc_j)A_{ji}=v_i(1+tu_i)\quad\text{for every }i.$$ No simplex or sign assumptions are needed. This identifies coefficient perturbations with the fitted-value paths used in the second-order calculation.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivityAnalytic.lean#L121-L141

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

theorem ReweightedNPMLE.finiteMixtureValue_add_smul_eq_mul_one_add_relative
    {k n : ℕ} (A : Fin k → Fin n → ℝ) (v : Fin n → ℝ)
    (p : Fin k → ℝ) (hpv : finiteMixtureValue A p = v)
    (hv : ∀ i, v i ≠ 0) (c : Fin k → ℝ) (t : ℝ) :
    finiteMixtureValue A (p + t • c) =
      fun i ↦ v i * (1 + t * relativeDictionaryMap A v c i) := by sorry
