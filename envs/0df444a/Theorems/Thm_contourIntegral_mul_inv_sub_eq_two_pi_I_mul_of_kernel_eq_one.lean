-- Prove2me | Theorems.Thm_contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_kernel_eq_one
-- name    : contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_kernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:37.260159+00:00
-- url     : https://prove2.me/theorems/510f7f56-cb01-5915-9512-d581da3fa5f0
-- title:
--   contour Integral mul inv sub eq two pi I mul of kernel eq one: contour Integral mul inv sub eq two pi I mul of kernel eq one
-- statement:
--   Cauchy's formula with the boundary datum placed before the scalar kernel,
--   matching the exterior-kernel approximation interface.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L143-L153
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L143-L153

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology

theorem contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_kernel_eq_one
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) {z : ℂ}
    (hz : z ∈ Omega.carrier)
    (hkernel : crouzeixScalarCauchyKernel Omega z = 1) :
    contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by sorry
