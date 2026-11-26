-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_eq_iff_sub_C_eval_zero
-- name    : crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_eq_iff_sub_C_eval_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:19:38.94603+00:00
-- url     : https://prove2.me/theorems/2f0c1967-9ee0-5b76-bcd3-1237deab3ae7
-- title:
--   crouzeix Auxiliary Operator scalar Companion Closed Extension eq iff sub C eval zero: crouzeix Auxiliary Operator scalar Companion Closed Extension eq iff sub C eval zero
-- statement:
--   In particular, contour reproduction for `p` is equivalent to contour
--   reproduction after normalizing its value at zero to vanish.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L314-L337
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L314-L337

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_eq_iff_sub_C_eval_zero
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    (crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p) ↔
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega
            (p - Polynomial.C (Polynomial.eval 0 p))) =
        crouzeixPolynomialAuxiliaryOperator A Omega
          (p - Polynomial.C (Polynomial.eval 0 p)) := by sorry
