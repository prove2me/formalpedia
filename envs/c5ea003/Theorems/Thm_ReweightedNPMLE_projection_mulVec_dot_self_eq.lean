-- Prove2me | Theorems.Thm_ReweightedNPMLE_projection_mulVec_dot_self_eq
-- name    : ReweightedNPMLE.projection_mulVec_dot_self_eq
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:12.182774+00:00
-- url     : https://prove2.me/theorems/81fce0c0-8226-4c4f-81ce-73ed55cd76a3
-- title:
--   Norm identity for an orthogonal projection matrix
-- statement:
--   Let $V\in\mathbb R^{n\times k}$ satisfy $V^\mathsf TV=I_k$, and put $s=VV^\mathsf Tx$. Then for every $x\in\mathbb R^n$, $$\langle s,s\rangle=\langle x,s\rangle.$$ Finite empty index sets are allowed. This identity gives the exact quadratic value attained by the projected tangent direction.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SupportSensitivityAnalytic.lean#L289-L323

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

theorem ReweightedNPMLE.projection_mulVec_dot_self_eq {n k : Type*}
    [Fintype n] [Fintype k] [DecidableEq k]
    (V : Matrix n k ℝ) (hV : Vᴴ * V = 1) (x : n → ℝ) :
    let s := (V * Vᴴ) *ᵥ x
    dotProduct s s = dotProduct x s := by sorry
