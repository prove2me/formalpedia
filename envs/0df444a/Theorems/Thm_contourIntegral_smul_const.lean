-- Prove2me | Theorems.Thm_contourIntegral_smul_const
-- name    : contourIntegral_smul_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:49.919281+00:00
-- url     : https://prove2.me/theorems/5319f011-6f16-5f2c-adc3-a4284cec270b
-- title:
--   contour Integral smul const: contour Integral smul const
-- statement:
--   A fixed vector can be moved through a scalar-weighted contour integral.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L64-L72
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L64-L72

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem contourIntegral_smul_const
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : ℂ → ℂ) (b : F) (gamma : ℝ → ℂ) :
    contourIntegral (fun z => f z • b) gamma =
      contourIntegral f gamma • b := by sorry
