-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_smul_iff
-- name    : crouzeixBoundaryPhaseContractive_smul_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:44:14.240836+00:00
-- url     : https://prove2.me/theorems/4eff360c-a634-5af2-bda8-6f194edb27c2
-- title:
--   crouzeix Boundary Phase Contractive smul iff: crouzeix Boundary Phase Contractive smul iff
-- statement:
--   Scaling by a nonzero scalar preserves and reflects phase contractivity.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L77-L87
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L77-L87

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u

theorem crouzeixBoundaryPhaseContractive_smul_iff
    (Omega : SmoothJordanDomain) {a : ℂ} (ha : a ≠ 0)
    (p : Polynomial ℂ) :
    CrouzeixBoundaryPhaseContractive Omega (a • p) ↔
      CrouzeixBoundaryPhaseContractive Omega p := by sorry
