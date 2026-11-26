-- Prove2me | Theorems.Thm_hasDerivAt_resolvent_affineOperator
-- name    : hasDerivAt_resolvent_affineOperator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:01.729812+00:00
-- url     : https://prove2.me/theorems/5fe7eba7-f521-569a-9750-8dee3c1d2ef9
-- title:
--   has Deriv At resolvent affine Operator: has Deriv At resolvent affine Operator
-- statement:
--   The has Deriv At resolvent affine Operator construction uses the has Deriv At resolvent affine Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L23-L33
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ResolventContourHomotopy.lean#L23-L33

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem hasDerivAt_resolvent_affineOperator
    (B D : E →L[ℂ] E) (s z : ℂ)
    (hres : z ∈ resolventSet ℂ (B + s • D)) :
    HasDerivAt (fun w : ℂ => resolvent (B + w • D) z)
      (resolvent (B + s • D) z * D * resolvent (B + s • D) z) s := by sorry
