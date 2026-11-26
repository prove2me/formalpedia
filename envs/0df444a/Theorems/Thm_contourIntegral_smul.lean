-- Prove2me | Theorems.Thm_contourIntegral_smul
-- name    : contourIntegral_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:14.554127+00:00
-- url     : https://prove2.me/theorems/0272de83-fdd7-4f2d-a470-0c749692fc2f
-- title:
--   contour Integral smul: contour Integral smul
-- statement:
--   The contour Integral smul construction uses the contour Integral smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L86-L92
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L86-L92

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem contourIntegral_smul (a : ℂ) (f : ℂ → F) (γ : ℝ → ℂ) :
    contourIntegral (fun z => a • f z) γ = a • contourIntegral f γ := by sorry
