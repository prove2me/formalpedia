-- Prove2me | Theorems.Thm_norm_eval_star_smul_add_C_star_sub_scalarCompanionClosedExtension_affine
-- name    : norm_eval_star_smul_add_C_star_sub_scalarCompanionClosedExtension_affine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:48:12.795828+00:00
-- url     : https://prove2.me/theorems/cc1cf2ff-1ce9-4aff-af14-0f1ab388d80e
-- title:
--   norm eval star smul add C star sub scalar Companion Closed Extension affine: norm eval star smul add C star sub scalar Companion Closed Extension affine
-- statement:
--   The preceding affine transfer has an exact pointwise error identity.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2065-L2081
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L2065-L2081

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem norm_eval_star_smul_add_C_star_sub_scalarCompanionClosedExtension_affine
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (a b : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖Polynomial.eval z ((star a) • q + Polynomial.C (star b)) -
        crouzeixPolynomialScalarCompanionClosedExtension
          Omega (a • p + Polynomial.C b) z‖ =
      ‖a‖ *
        ‖Polynomial.eval z q -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ := by sorry
