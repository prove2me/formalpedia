-- Prove2me | Theorems.Thm_contourIntegral_circleMap
-- name    : contourIntegral_circleMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:29:48.971412+00:00
-- url     : https://prove2.me/theorems/d625f18b-aaff-4065-96f7-db63e6833fbd
-- title:
--   contour Integral circle Map: contour Integral circle Map
-- statement:
--   Along the circle parameterization `circleMap c R` the contour integral is Mathlib's
--   `circleIntegral`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L48-L49
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L48-L49

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem contourIntegral_circleMap (f : ℂ → F) (c : ℂ) (R : ℝ) :
    contourIntegral f (circleMap c R) = circleIntegral f c R := by sorry
