-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_of_dividedDifference_induction
-- name    : crouzeixBoundaryPhaseContractive_of_dividedDifference_induction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:16.884796+00:00
-- url     : https://prove2.me/theorems/54a6e449-0d16-531b-b076-b791ce31194a
-- title:
--   crouzeix Boundary Phase Contractive of divided Difference induction: crouzeix Boundary Phase Contractive of divided Difference induction
-- statement:
--   To establish sharp boundary-phase contractivity for every polynomial, it
--   suffices to propagate it from all frontier-indexed divided differences to a
--   positive-degree parent polynomial.  The degree-zero base is automatic.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L127-L138
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L127-L138

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u

theorem crouzeixBoundaryPhaseContractive_of_dividedDifference_induction
    (Omega : SmoothJordanDomain)
    (hstep : ∀ p, 0 < p.natDegree →
      (∀ xi ∈ frontier Omega.carrier,
        CrouzeixBoundaryPhaseContractive Omega
          (p /ₘ (Polynomial.X - Polynomial.C xi))) →
      CrouzeixBoundaryPhaseContractive Omega p) :
    ∀ p, CrouzeixBoundaryPhaseContractive Omega p := by sorry
