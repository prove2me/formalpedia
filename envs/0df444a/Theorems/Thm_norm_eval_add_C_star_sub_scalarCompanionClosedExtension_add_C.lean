-- Prove2me | Theorems.Thm_norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
-- name    : norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:08:47.604493+00:00
-- url     : https://prove2.me/theorems/07b7a114-27b7-55bc-9bee-f4c2083a71dc
-- title:
--   norm eval add C star sub scalar Companion Closed Extension add C: norm eval add C star sub scalar Companion Closed Extension add C
-- statement:
--   Shifting an approximating polynomial by the conjugate constant preserves
--   the approximation error for the correspondingly shifted closed companion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1946-L1962
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadial.lean#L1946-L1962

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem norm_eval_add_C_star_sub_scalarCompanionClosedExtension_add_C
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    ‖Polynomial.eval z (q + Polynomial.C (star a)) -
        crouzeixPolynomialScalarCompanionClosedExtension
          Omega (p + Polynomial.C a) z‖ =
      ‖Polynomial.eval z q -
        crouzeixPolynomialScalarCompanionClosedExtension Omega p z‖ := by sorry
