-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_smul
-- name    : crouzeixAuxiliaryOperator_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:25.686357+00:00
-- url     : https://prove2.me/theorems/c266cfd1-ba3e-4089-95a3-678f08f497fd
-- title:
--   crouzeix Auxiliary Operator smul: crouzeix Auxiliary Operator smul
-- statement:
--   The auxiliary operator is complex-linear in its scalar boundary datum.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L408-L420
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L408-L420

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem crouzeixAuxiliaryOperator_smul (A : E →L[ℂ] E)
    (Omega : SmoothJordanDomain) (a : ℂ) (h : ℂ → ℂ) :
    crouzeixAuxiliaryOperator A Omega (fun z => a • h z) =
      a • crouzeixAuxiliaryOperator A Omega h := by sorry
