-- Prove2me | Theorems.Thm_contourIntegral_inv_sub_mul_eq_two_pi_I_mul_of_kernel_eq_one
-- name    : contourIntegral_inv_sub_mul_eq_two_pi_I_mul_of_kernel_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:54.728011+00:00
-- url     : https://prove2.me/theorems/4b08023e-5625-4067-811a-d99e807e68bd
-- title:
--   contour Integral inv sub mul eq two pi I mul of kernel eq one: contour Integral inv sub mul eq two pi I mul of kernel eq one
-- statement:
--   Cauchy's formula on a smooth Jordan carrier at a point where the
--   normalized scalar winding kernel is one.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L110-L139
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L110-L139

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology

theorem contourIntegral_inv_sub_mul_eq_two_pi_I_mul_of_kernel_eq_one
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) {z : ℂ}
    (hz : z ∈ Omega.carrier)
    (hkernel : crouzeixScalarCauchyKernel Omega z = 1) :
    contourIntegral (fun sigma => (sigma - z)⁻¹ * f sigma)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by sorry
