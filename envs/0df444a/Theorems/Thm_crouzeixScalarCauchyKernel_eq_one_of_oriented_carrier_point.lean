-- Prove2me | Theorems.Thm_crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
-- name    : crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:41:34.709855+00:00
-- url     : https://prove2.me/theorems/a7f06c32-12ca-40ee-9b0b-a8ecefdf24de
-- title:
--   crouzeix Scalar Cauchy Kernel eq one of oriented carrier point: crouzeix Scalar Cauchy Kernel eq one of oriented carrier point
-- statement:
--   A consistently oriented carrier point has normalized scalar winding one.
--   The proof obtains the total argument change from the logarithmic-derivative
--   ODE and uses convexity to exclude every positive integer other than one.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelWinding.lean#L123-L311
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelWinding.lean#L123-L311

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real

theorem crouzeixScalarCauchyKernel_eq_one_of_oriented_carrier_point
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    crouzeixScalarCauchyKernel Omega c = 1 := by sorry
