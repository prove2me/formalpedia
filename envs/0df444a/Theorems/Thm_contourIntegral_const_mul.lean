-- Prove2me | Theorems.Thm_contourIntegral_const_mul
-- name    : contourIntegral_const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:24.049291+00:00
-- url     : https://prove2.me/theorems/ec450997-5374-49b4-891d-58137c0c15c5
-- title:
--   contour Integral const mul: contour Integral const mul
-- statement:
--   A constant left factor moves through a contour integral in a complex Banach algebra.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L109-L113
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L109-L113

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
variable {B : Type*} [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B]

theorem contourIntegral_const_mul {f : ℂ → B} {γ : ℝ → ℂ} (b : B)
    (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => b * f z) γ = b * contourIntegral f γ := by sorry
