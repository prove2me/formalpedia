-- Prove2me | Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
-- name    : continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:36:04.47856+00:00
-- url     : https://prove2.me/theorems/9f4bd851-5002-5134-ab8c-4a9e56395183
-- title:
--   continuous On crouzeix Polynomial Scalar Companion Closed Extension of tendsto: continuous On crouzeix Polynomial Scalar Companion Closed Extension of tendsto
-- statement:
--   If `b z` is the interior limit of the scalar companion at every frontier
--   point, the canonical extension is continuous on the whole closed domain.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L55-L70
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionBoundary.lean#L55-L70

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
set_option autoImplicit false
open Complex Filter Set

theorem continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_of_tendsto
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (b : ℂ → ℂ)
    (hlim : ∀ z ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanion Omega p)
        (nhdsWithin z Omega.carrier) (nhds (b z))) :
    ContinuousOn
      (crouzeixPolynomialScalarCompanionClosedExtension Omega p)
      (closure Omega.carrier) := by sorry
