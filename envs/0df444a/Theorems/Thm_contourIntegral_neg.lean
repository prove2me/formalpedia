-- Prove2me | Theorems.Thm_contourIntegral_neg
-- name    : contourIntegral_neg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:30:13.145378+00:00
-- url     : https://prove2.me/theorems/d9988200-a324-4b7f-89a5-f218e9bd6794
-- title:
--   contour Integral neg: contour Integral neg
-- statement:
--   The contour Integral neg construction uses the contour Integral neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L73-L77
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L73-L77

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem contourIntegral_neg (f : ℂ → F) (γ : ℝ → ℂ) :
    contourIntegral (fun z => -f z) γ = -contourIntegral f γ := by sorry
