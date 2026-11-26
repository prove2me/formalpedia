-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_smul
-- name    : crouzeixBoundaryPhaseContractive_smul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:57:36.704025+00:00
-- url     : https://prove2.me/theorems/b59ea855-dd24-484d-afc9-823b7393d880
-- title:
--   crouzeix Boundary Phase Contractive smul: crouzeix Boundary Phase Contractive smul
-- statement:
--   Phase contractivity is preserved by polynomial scaling.  Both the
--   boundary value and the frontier sup norm scale by the norm of the scalar.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L59-L74
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L59-L74

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u

theorem crouzeixBoundaryPhaseContractive_smul
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hp : CrouzeixBoundaryPhaseContractive Omega p) :
    CrouzeixBoundaryPhaseContractive Omega (a • p) := by sorry
