-- Prove2me | Theorems.Thm_crouzeixAuxiliaryOperator_congr_closure
-- name    : crouzeixAuxiliaryOperator_congr_closure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:01:55.654798+00:00
-- url     : https://prove2.me/theorems/031a5831-a88a-555e-bcd6-1be3df617b8d
-- title:
--   crouzeix Auxiliary Operator congr closure: crouzeix Auxiliary Operator congr closure
-- statement:
--   Equality on the carrier closure is therefore also sufficient.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L116-L122
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionRadialAssembly.lean#L116-L122

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
omit [CompleteSpace E]

theorem crouzeixAuxiliaryOperator_congr_closure
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (f g : ℂ → ℂ)
    (hfg : Set.EqOn f g (closure Omega.carrier)) :
    crouzeixAuxiliaryOperator A Omega f =
      crouzeixAuxiliaryOperator A Omega g := by sorry
