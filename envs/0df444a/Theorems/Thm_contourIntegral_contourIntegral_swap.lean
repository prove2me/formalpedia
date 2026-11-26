-- Prove2me | Theorems.Thm_contourIntegral_contourIntegral_swap
-- name    : contourIntegral_contourIntegral_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:54:37.408175+00:00
-- url     : https://prove2.me/theorems/bd8f46b2-d724-5a10-93a3-14962eb9003f
-- title:
--   contour Integral contour Integral swap: contour Integral contour Integral swap
-- statement:
--   Fubini's theorem for two contour integrals, with the exact product
--   integrability hypothesis on the derivative-weighted kernel.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L209-L261
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventCauchyKernel.lean#L209-L261

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem contourIntegral_contourIntegral_swap
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → ℂ → F) (gamma delta : ℝ → ℂ)
    (hint : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ =>
      deriv gamma x.1 •
        (deriv delta x.2 • f (gamma x.1) (delta x.2)))
      (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ
        uIoc (0 : ℝ) (2 * Real.pi))) :
    contourIntegral (fun z => contourIntegral (f z) delta) gamma =
      contourIntegral (fun w => contourIntegral (fun z => f z w) gamma)
        delta := by sorry
