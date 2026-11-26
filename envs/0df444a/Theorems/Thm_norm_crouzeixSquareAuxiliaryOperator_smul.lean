-- Prove2me | Theorems.Thm_norm_crouzeixSquareAuxiliaryOperator_smul
-- name    : norm_crouzeixSquareAuxiliaryOperator_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:33:49.47041+00:00
-- url     : https://prove2.me/theorems/faed2f3e-e77c-5126-bc7f-0ffb157ca533
-- title:
--   norm crouzeix Square Auxiliary Operator smul: norm crouzeix Square Auxiliary Operator smul
-- statement:
--   The scalar-square main auxiliary operator has the corresponding
--   degree-two norm homogeneity.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L442-L448
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L442-L448

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_crouzeixSquareAuxiliaryOperator_smul (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) :
    ‖crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z (a • p)) * Polynomial.eval z (a • p))‖ =
      ‖a‖ ^ 2 * ‖crouzeixAuxiliaryOperator A Omega
        (fun z => star (Polynomial.eval z p) * Polynomial.eval z p)‖ := by sorry
