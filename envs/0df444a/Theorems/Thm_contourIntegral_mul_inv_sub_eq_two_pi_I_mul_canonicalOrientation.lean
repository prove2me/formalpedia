-- Prove2me | Theorems.Thm_contourIntegral_mul_inv_sub_eq_two_pi_I_mul_canonicalOrientation
-- name    : contourIntegral_mul_inv_sub_eq_two_pi_I_mul_canonicalOrientation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:41:54.948016+00:00
-- url     : https://prove2.me/theorems/9308f392-1e87-52bd-bfe8-931a5015d3e9
-- title:
--   contour Integral mul inv sub eq two pi I mul canonical Orientation: contour Integral mul inv sub eq two pi I mul canonical Orientation
-- statement:
--   The canonical orientation of every smooth convex Jordan domain satisfies
--   the winding-one Cauchy integral formula.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L175-L193
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L175-L193

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology

theorem contourIntegral_mul_inv_sub_eq_two_pi_I_mul_canonicalOrientation
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.canonicalOrientation.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by sorry
