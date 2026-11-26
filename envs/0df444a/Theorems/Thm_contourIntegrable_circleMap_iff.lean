-- Prove2me | Theorems.Thm_contourIntegrable_circleMap_iff
-- name    : contourIntegrable_circleMap_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:29:47.873679+00:00
-- url     : https://prove2.me/theorems/0763f266-573f-49fd-b2bb-49aac3e2ac65
-- title:
--   contour Integrable circle Map iff: contour Integrable circle Map iff
-- statement:
--   Along the circle parameterization `circleMap c R` contour integrability is Mathlib's
--   `CircleIntegrable`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L53-L55
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L53-L55

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem contourIntegrable_circleMap_iff {f : ℂ → F} {c : ℂ} (R : ℝ) :
    ContourIntegrable f (circleMap c R) ↔ CircleIntegrable f c R := by sorry
