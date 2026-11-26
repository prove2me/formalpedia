-- Prove2me | Theorems.Thm_crouzeixAuxiliaryIntegrand_contourIntegrable
-- name    : crouzeixAuxiliaryIntegrand_contourIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:31.40196+00:00
-- url     : https://prove2.me/theorems/d8f23688-237b-5caa-8ef5-c839039e3949
-- title:
--   crouzeix Auxiliary Integrand contour Integrable: crouzeix Auxiliary Integrand contour Integrable
-- statement:
--   A continuous scalar boundary datum gives a contour-integrable
--   operator-valued resolvent kernel.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L84-L95
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L84-L95

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

theorem crouzeixAuxiliaryIntegrand_contourIntegrable [CompleteSpace E] (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hh : ContinuousOn h (Omega.boundaryParam '' Icc (0 : ℝ) (2 * Real.pi))) :
    ContourIntegrable (fun z => h z • resolvent A z) Omega.boundaryParam := by sorry
