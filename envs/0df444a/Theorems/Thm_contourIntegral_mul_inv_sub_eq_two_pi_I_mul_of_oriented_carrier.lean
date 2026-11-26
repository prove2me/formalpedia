-- Prove2me | Theorems.Thm_contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_oriented_carrier
-- name    : contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_oriented_carrier
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:16.455843+00:00
-- url     : https://prove2.me/theorems/096b1ae8-d55b-41e0-8f18-29e374265be6
-- title:
--   contour Integral mul inv sub eq two pi I mul of oriented carrier: contour Integral mul inv sub eq two pi I mul of oriented carrier
-- statement:
--   Consistent supporting-normal orientation supplies the winding-one
--   hypothesis in Cauchy's formula.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L157-L171
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanCauchyFormula.lean#L157-L171

import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchy
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Mathlib.Analysis.Complex.RemovableSingularity
import Definitions.Def_Operator_Crouzeix_SmoothJordanCauchyFormula
set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Topology

theorem contourIntegral_mul_inv_sub_eq_two_pi_I_mul_of_oriented_carrier
    (Omega : SmoothJordanDomain) {f : ℂ → ℂ}
    (hf : DiffContOnCl ℂ f Omega.carrier)
    (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    contourIntegral (fun sigma => f sigma * (sigma - z)⁻¹)
        Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) * f z := by sorry
