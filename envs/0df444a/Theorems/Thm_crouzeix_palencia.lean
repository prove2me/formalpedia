-- Prove2me | Theorems.Thm_crouzeix_palencia
-- name    : crouzeix_palencia
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:43:03.882909+00:00
-- url     : https://prove2.me/theorems/0a8d0c4b-fefb-44f1-b45c-5b105b52f407
-- title:
--   crouzeix palencia: crouzeix palencia
-- statement:
--   The exact Crouzeix--Palencia theorem: the closed numerical range is a
--   `1 + sqrt 2` polynomial spectral set for every bounded operator on a complex
--   Hilbert space.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L134-L150
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothSupportDomain.lean#L134-L150

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
