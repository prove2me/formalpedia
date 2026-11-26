-- Prove2me | Theorems.Thm_norm_crouzeixAuxiliaryOperator_le
-- name    : norm_crouzeixAuxiliaryOperator_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:35:39.024892+00:00
-- url     : https://prove2.me/theorems/8530f9d9-ccb2-5170-8299-8cc9e5971de9
-- title:
--   norm crouzeix Auxiliary Operator le: norm crouzeix Auxiliary Operator le
-- statement:
--   A pointwise bound `C` on the parameterized resolvent kernel gives the
--   corresponding explicit operator-norm bound for the normalized auxiliary
--   operator.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L160-L170
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AuxOperator.lean#L160-L170

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

theorem norm_crouzeixAuxiliaryOperator_le (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (h : ℂ → ℂ) {C : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (h (Omega.boundaryParam t) • resolvent A (Omega.boundaryParam t))‖ ≤ C) :
    ‖crouzeixAuxiliaryOperator A Omega h‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by sorry
