-- Prove2me | Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_cocompact
-- name    : tendsto_crouzeixPolynomialScalarCompanion_cocompact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:31.964816+00:00
-- url     : https://prove2.me/theorems/1b6b6cc9-ff44-5336-ae44-86da56cd6551
-- title:
--   tendsto crouzeix Polynomial Scalar Companion cocompact: tendsto crouzeix Polynomial Scalar Companion cocompact
-- statement:
--   The exterior scalar companion has the canonical Cauchy-transform
--   normalization: it tends to zero at infinity.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L215-L246
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionDecay.lean#L215-L246

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real

theorem tendsto_crouzeixPolynomialScalarCompanion_cocompact
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (cocompact ℂ) (nhds 0) := by sorry
