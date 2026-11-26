-- Prove2me | Theorems.Thm_crouzeix_palencia_of_convexThickening_hasMergelyanPolynomialApproximation
-- name    : crouzeix_palencia_of_convexThickening_hasMergelyanPolynomialApproximation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:51.773288+00:00
-- url     : https://prove2.me/theorems/10c98288-cfd3-4d8f-a894-538c80540398
-- title:
--   crouzeix palencia of convex Thickening has Mergelyan Polynomial Approximation: crouzeix palencia of convex Thickening has Mergelyan Polynomial Approximation
-- statement:
--   Textbook explicit-thickening criterion: if the explicit metric
--   thickenings of the closed numerical range admit smooth Jordan realizations
--   with the Mergelyan polynomial approximation property, then the exact
--   Crouzeix--Palencia bound follows.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1199-L1221
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanExhaustion.lean#L1199-L1221

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

theorem crouzeix_palencia_of_convexThickening_hasMergelyanPolynomialApproximation
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hmergelyan : ∀ n,
      (Omega n).HasMergelyanPolynomialApproximation) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
