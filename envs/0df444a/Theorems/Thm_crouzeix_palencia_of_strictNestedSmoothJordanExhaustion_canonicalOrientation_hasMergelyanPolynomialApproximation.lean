-- Prove2me | Theorems.Thm_crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_hasMergelyanPolynomialApproximation
-- name    : crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_hasMergelyanPolynomialApproximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:51:40.094073+00:00
-- url     : https://prove2.me/theorems/28d3a722-9756-5bbe-bfe7-7cd211b3baa4
-- title:
--   crouzeix palencia of strict Nested Smooth Jordan Exhaustion canonical Orientation has Mergelyan Polynomial Approximation: crouzeix palencia of strict Nested Smooth Jordan Exhaustion canonical Orientat
-- statement:
--   Textbook terminal criterion: a strictly nested smooth exhaustion whose
--   canonically oriented stages satisfy the Mergelyan polynomial approximation
--   property yields the exact Crouzeix--Palencia bound.  The regularity theorem
--   above applies that property automatically to every closed scalar companion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1175-L1193
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1175-L1193

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_hasMergelyanPolynomialApproximation
    (A : E →L[ℂ] E)
    (Omega : StrictNestedSmoothJordanExhaustion
      (closure (numericalRange A)))
    (hmergelyan : ∀ n,
      (Omega.domain n).HasMergelyanPolynomialApproximation) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
