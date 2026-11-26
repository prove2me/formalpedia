-- Prove2me | Theorems.Thm_contourIntegral_mul_const
-- name    : contourIntegral_mul_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:06.901685+00:00
-- url     : https://prove2.me/theorems/797bbd3a-1005-4653-a62d-ab35676b9e23
-- title:
--   contour Integral mul const: contour Integral mul const
-- statement:
--   A constant right factor moves through a contour integral in a complex Banach algebra.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L116-L121
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L116-L121

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

theorem contourIntegral_mul_const {f : ℂ → B} {γ : ℝ → ℂ} (b : B)
    (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => f z * b) γ = contourIntegral f γ * b := by sorry
