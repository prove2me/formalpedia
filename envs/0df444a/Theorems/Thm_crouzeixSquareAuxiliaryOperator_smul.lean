-- Prove2me | Theorems.Thm_crouzeixSquareAuxiliaryOperator_smul
-- name    : crouzeixSquareAuxiliaryOperator_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:20.255242+00:00
-- url     : https://prove2.me/theorems/458c7e22-330c-4651-b112-8f65e91717de
-- title:
--   crouzeix Square Auxiliary Operator smul: crouzeix Square Auxiliary Operator smul
-- statement:
--   The scalar-square main auxiliary operator is homogeneous of degree two
--   under polynomial scaling.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L424-L438
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L424-L438

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixSquareAuxiliaryOperator_smul (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z (a • p)) * Polynomial.eval z (a • p)) =
      (star a * a) • crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p) := by sorry
