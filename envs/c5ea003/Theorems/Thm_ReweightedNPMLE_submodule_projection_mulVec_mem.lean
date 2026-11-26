-- Prove2me | Theorems.Thm_ReweightedNPMLE_submodule_projection_mulVec_mem
-- name    : ReweightedNPMLE.submodule_projection_mulVec_mem
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:10.03824+00:00
-- url     : https://prove2.me/theorems/bbb8295a-64b9-51b3-a2f9-878a8e9dbcaf
-- title:
--   The orthonormal-basis projection maps into its subspace
-- statement:
--   Let $S\subset\mathbb R^n$ be a linear subspace, and let $V\in\mathbb R^{n\times\dim S}$ have columns equal to its canonical orthonormal basis. For every $x\in\mathbb R^n$, $$VV^\mathsf Tx\in S.$$ This identifies the matrix projection used to turn directional sensitivity into a matrix inequality.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivityAnalytic.lean#L268-L287

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

theorem ReweightedNPMLE.submodule_projection_mulVec_mem {n : ℕ}
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (x : Fin n → ℝ) :
    WithLp.toLp 2 (((submoduleOrthonormalMatrix S) *
      (submoduleOrthonormalMatrix S)ᴴ) *ᵥ x) ∈ S := by sorry
