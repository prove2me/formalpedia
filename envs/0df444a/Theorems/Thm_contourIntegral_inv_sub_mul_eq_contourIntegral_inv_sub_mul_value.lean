-- Prove2me | Theorems.Thm_contourIntegral_inv_sub_mul_eq_contourIntegral_inv_sub_mul_value
-- name    : contourIntegral_inv_sub_mul_eq_contourIntegral_inv_sub_mul_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:41:34.756194+00:00
-- url     : https://prove2.me/theorems/4d03b8a2-33c0-5f5a-b867-b7f95200d590
-- title:
--   contour Integral inv sub mul eq contour Integral inv sub mul value: contour Integral inv sub mul eq contour Integral inv sub mul value
-- statement:
--   Cauchy's formula before winding normalization: the contour integral of
--   `(sigma - z)⁻¹ f(sigma)` is the raw scalar contour mass times `f z`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L32-L106
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L32-L106

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology

theorem contourIntegral_inv_sub_mul_eq_contourIntegral_inv_sub_mul_value
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier) {z : ℂ}
    (hz : z ∈ Omega.carrier) :
    contourIntegral (fun sigma => (sigma - z)⁻¹ * f sigma)
        Omega.boundaryParam =
      contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
        Omega.boundaryParam * f z := by sorry
