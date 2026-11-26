-- Prove2me | Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
-- name    : crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:40.33738+00:00
-- url     : https://prove2.me/theorems/0b4d17a9-a508-48d2-b726-f304785a9a1c
-- title:
--   crouzeix Scalar Cauchy Kernel eq one of oriented carrier: crouzeix Scalar Cauchy Kernel eq one of oriented carrier
-- statement:
--   Consistent orientation at one carrier point forces winding normalization
--   at every point of the strictly convex carrier.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelWinding.lean#L315-L323
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelWinding.lean#L315-L323

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    ∀ z ∈ Omega.carrier, crouzeixScalarCauchyKernel Omega z = 1 := by sorry
