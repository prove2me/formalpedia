-- Prove2me | Theorems.Thm_exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator
-- name    : exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:03:18.256739+00:00
-- url     : https://prove2.me/theorems/e30bca02-c3cf-530d-992d-e561ef9e357a
-- title:
--   exists smooth Jordan Domain norm bound crouzeix Polynomial Auxiliary Operator: exists smooth Jordan Domain norm bound crouzeix Polynomial Auxiliary Operator
-- statement:
--   Every polynomial admits a normalized auxiliary operator on some smooth
--   Jordan domain containing `closure (numericalRange A)`, together with a finite
--   contour-length norm bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L199-L207
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L199-L207

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

theorem exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator
    [CompleteSpace E] (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    ∃ (Omega : SmoothJordanDomain) (C : ℝ),
      closure (numericalRange A) ⊆ Omega.carrier ∧
      ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
        ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by sorry
