-- Prove2me | Theorems.Thm_crouzeixScalarCauchyKernel_eq_zero_of_not_mem_closure_carrier
-- name    : crouzeixScalarCauchyKernel_eq_zero_of_not_mem_closure_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:13.188802+00:00
-- url     : https://prove2.me/theorems/95aabf67-0ac4-47f2-8f8f-394bf149909d
-- title:
--   crouzeix Scalar Cauchy Kernel eq zero of not mem closure carrier: crouzeix Scalar Cauchy Kernel eq zero of not mem closure carrier
-- statement:
--   The normalized scalar Cauchy kernel is zero throughout the exterior of
--   the closed convex carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L206-L212
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L206-L212

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixScalarCauchyKernel_eq_zero_of_not_mem_closure_carrier
    (Omega : SmoothJordanDomain) {z : ℂ}
    (hz : z ∉ closure Omega.carrier) :
    crouzeixScalarCauchyKernel Omega z = 0 := by sorry
