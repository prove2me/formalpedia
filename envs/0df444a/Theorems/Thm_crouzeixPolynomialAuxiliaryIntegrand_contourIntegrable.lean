-- Prove2me | Theorems.Thm_crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
-- name    : crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:35:43.662968+00:00
-- url     : https://prove2.me/theorems/e30af137-a261-4634-bb1f-9c1b1ef4bdf0
-- title:
--   crouzeix Polynomial Auxiliary Integrand contour Integrable: crouzeix Polynomial Auxiliary Integrand contour Integrable
-- statement:
--   The conjugate polynomial boundary datum produces an integrable
--   operator-valued resolvent kernel.  This is the specialization used in the
--   Crouzeix--Palencia symmetrized and product estimates.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L107-L113
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L107-L113

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_NumericalRange_Bounded
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Definitions.Def_Operator_Crouzeix_AuxOperator
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Real Interval
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ContourIntegrable (fun z => star (Polynomial.eval z p) • resolvent A z)
      Omega.boundaryParam := by sorry
