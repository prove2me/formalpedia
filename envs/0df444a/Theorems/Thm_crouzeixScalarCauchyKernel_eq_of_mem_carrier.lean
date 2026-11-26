-- Prove2me | Theorems.Thm_crouzeixScalarCauchyKernel_eq_of_mem_carrier
-- name    : crouzeixScalarCauchyKernel_eq_of_mem_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:17.27529+00:00
-- url     : https://prove2.me/theorems/5b614230-6269-42a1-8eff-3105495019df
-- title:
--   crouzeix Scalar Cauchy Kernel eq of mem carrier: crouzeix Scalar Cauchy Kernel eq of mem carrier
-- statement:
--   The normalized scalar Cauchy kernel is constant on the open strictly
--   convex carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L83-L105
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L83-L105

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem crouzeixScalarCauchyKernel_eq_of_mem_carrier
    (Omega : SmoothJordanDomain) {z w : ℂ}
    (hz : z ∈ Omega.carrier) (hw : w ∈ Omega.carrier) :
    crouzeixScalarCauchyKernel Omega z =
      crouzeixScalarCauchyKernel Omega w := by sorry
