-- Prove2me | Theorems.Thm_contourIntegral_sub
-- name    : contourIntegral_sub
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:30:11.363204+00:00
-- url     : https://prove2.me/theorems/397df93e-0379-59d5-858b-83a16faa8596
-- title:
--   contour Integral sub: contour Integral sub
-- statement:
--   The contour Integral sub construction uses the contour Integral sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L79-L84
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L79-L84

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem contourIntegral_sub {f g : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ)
    (hg : ContourIntegrable g γ) :
    contourIntegral (fun z => f z - g z) γ = contourIntegral f γ - contourIntegral g γ := by sorry
