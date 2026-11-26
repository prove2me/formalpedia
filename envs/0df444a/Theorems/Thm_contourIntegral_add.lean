-- Prove2me | Theorems.Thm_contourIntegral_add
-- name    : contourIntegral_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:07.795034+00:00
-- url     : https://prove2.me/theorems/b0dd5da3-cc3d-5fbf-8e2e-5414b9b81e1b
-- title:
--   contour Integral add: contour Integral add
-- statement:
--   The contour Integral add construction uses the contour Integral add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L66-L71
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L66-L71

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem contourIntegral_add {f g : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ)
    (hg : ContourIntegrable g γ) :
    contourIntegral (fun z => f z + g z) γ = contourIntegral f γ + contourIntegral g γ := by sorry
