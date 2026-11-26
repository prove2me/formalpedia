-- Prove2me | Theorems.Thm_crouzeixBoundaryPhaseContractive_of_normalized
-- name    : crouzeixBoundaryPhaseContractive_of_normalized
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:59:37.990285+00:00
-- url     : https://prove2.me/theorems/ebf57516-c1b1-47d7-98d5-15f29e163dba
-- title:
--   crouzeix Boundary Phase Contractive of normalized: crouzeix Boundary Phase Contractive of normalized
-- statement:
--   On the infinite compact frontier of a smooth Jordan domain, it suffices
--   to prove phase contractivity for positive-degree polynomials normalized to
--   frontier sup norm one.  Exact conjugate homogeneity restores every nonzero
--   scale, while the degree-zero case is automatic.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L144-L185
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L144-L185

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u

theorem crouzeixBoundaryPhaseContractive_of_normalized
    (Omega : SmoothJordanDomain)
    (hnormalized : ∀ p : Polynomial ℂ, 0 < p.natDegree →
      polynomialSupNorm p (frontier Omega.carrier) = 1 →
      CrouzeixBoundaryPhaseContractive Omega p) :
    ∀ p, CrouzeixBoundaryPhaseContractive Omega p := by sorry
