-- Prove2me | Theorems.Thm_exists_norm_bound_crouzeixPolynomialAuxiliaryOperator
-- name    : exists_norm_bound_crouzeixPolynomialAuxiliaryOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:50.931504+00:00
-- url     : https://prove2.me/theorems/10f9319a-61ff-5f25-b377-0613f38bf5da
-- title:
--   exists norm bound crouzeix Polynomial Auxiliary Operator: exists norm bound crouzeix Polynomial Auxiliary Operator
-- statement:
--   For every containing smooth Jordan domain, the polynomial auxiliary
--   operator admits a finite explicit contour-length bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L188-L194
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L188-L194

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

theorem exists_norm_bound_crouzeixPolynomialAuxiliaryOperator [CompleteSpace E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier) :
    ∃ C : ℝ, ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by sorry
