-- Prove2me | Theorems.Thm_polynomial_induction_on_boundaryPhaseDividedDifferences
-- name    : polynomial_induction_on_boundaryPhaseDividedDifferences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:59:10.613632+00:00
-- url     : https://prove2.me/theorems/5048a38d-4c83-540a-9145-37538a9c84aa
-- title:
--   polynomial induction on boundary Phase Divided Differences: polynomial induction on boundary Phase Divided Differences
-- statement:
--   A branching strong-induction principle for the family of divided
--   differences indexed by the frontier.  Every quotient used in the positive
--   degree step is strictly lower-degree.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L92-L112
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCompanionPhaseInduction.lean#L92-L112

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u

theorem polynomial_induction_on_boundaryPhaseDividedDifferences
    (Omega : SmoothJordanDomain) (P : Polynomial ℂ → Prop)
    (hzero : ∀ p, p.natDegree = 0 → P p)
    (hstep : ∀ p, 0 < p.natDegree →
      (∀ xi ∈ frontier Omega.carrier,
        P (p /ₘ (Polynomial.X - Polynomial.C xi))) →
      P p) :
    ∀ p, P p := by sorry
