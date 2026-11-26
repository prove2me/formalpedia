-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero
-- name    : crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:57:40.601964+00:00
-- url     : https://prove2.me/theorems/6fc795b5-15ed-501f-9ddf-d67a2cd70be3
-- title:
--   crouzeix Boundary Phase Contractive of nat Degree eq zero: crouzeix Boundary Phase Contractive of nat Degree eq zero
-- statement:
--   Constant polynomials satisfy the sharp boundary-phase invariant.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L115-L122
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L115-L122

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u

theorem crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hp : p.natDegree = 0) :
    CrouzeixBoundaryPhaseContractive Omega p := by sorry
