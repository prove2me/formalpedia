-- Prove2me | Theorems.Thm_norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul
-- name    : norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:08:51.733965+00:00
-- url     : https://prove2.me/theorems/2151a795-8e90-53bb-9f03-83d88a3c8607
-- title:
--   norm eval star smul sub scalar Companion Closed Extension smul: norm eval star smul sub scalar Companion Closed Extension smul
-- statement:
--   Conjugate-scaling an approximating polynomial scales the closed-companion
--   approximation error by exactly the norm of the source scalar.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1995-L2010
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1995-L2010

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem norm_eval_star_smul_sub_scalarCompanionClosedExtension_smul
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖Polynomial.eval z ((star a) • q) -
        crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z‖ =
      ‖a‖ *
        ‖Polynomial.eval z q -
          crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ := by sorry
