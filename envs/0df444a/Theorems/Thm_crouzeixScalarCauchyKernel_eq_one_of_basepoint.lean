-- Prove2me | Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_basepoint
-- name    : crouzeixScalarCauchyKernel_eq_one_of_basepoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:23.058286+00:00
-- url     : https://prove2.me/theorems/0d0fcd23-61f1-5851-93ff-ad5a68fe85c9
-- title:
--   crouzeix Scalar Cauchy Kernel eq one of basepoint: crouzeix Scalar Cauchy Kernel eq one of basepoint
-- statement:
--   Winding normalization at one point of the carrier propagates to every
--   carrier point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L109-L115
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L109-L115

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixScalarCauchyKernel_eq_one_of_basepoint
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hkc : crouzeixScalarCauchyKernel Omega c = 1) :
    ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1 := by sorry
