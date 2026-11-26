-- Prove2me | Theorems.Thm_contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
-- name    : contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:41:35.549397+00:00
-- url     : https://prove2.me/theorems/7a21c09f-83b6-40c3-a337-36ed6aaa3597
-- title:
--   contour Integral inv sub eq zero of not mem closure carrier: contour Integral inv sub eq zero of not mem closure carrier
-- statement:
--   The scalar Cauchy contour vanishes at every point outside the closed
--   convex carrier.  Strict Hahn--Banach separation puts the entire boundary in
--   one branch of the complex logarithm, which supplies a global primitive for
--   the inverse kernel along the contour.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L121-L202
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ScalarCauchyKernelConstancy.lean#L121-L202

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
set_option autoImplicit false
open Complex Set
open scoped Interval Real

theorem contourIntegral_inv_sub_eq_zero_of_not_mem_closure_carrier
    (Omega : SmoothJordanDomain) {z : ℂ}
    (hz : z ∉ closure Omega.carrier) :
    contourIntegral (fun sigma : ℂ => (sigma - z)⁻¹)
      Omega.boundaryParam = 0 := by sorry
