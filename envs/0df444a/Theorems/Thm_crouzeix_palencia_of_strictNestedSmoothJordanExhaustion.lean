-- Prove2me | Theorems.Thm_crouzeix_palencia_of_strictNestedSmoothJordanExhaustion
-- name    : crouzeix_palencia_of_strictNestedSmoothJordanExhaustion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:23.561006+00:00
-- url     : https://prove2.me/theorems/02ed7205-bb6b-5b49-b84d-84f49460b8d7
-- title:
--   crouzeix palencia of strict Nested Smooth Jordan Exhaustion: crouzeix palencia of strict Nested Smooth Jordan Exhaustion
-- statement:
--   Every strict smooth-Jordan exhaustion of the closed numerical range gives
--   the exact Crouzeix--Palencia polynomial spectral-set bound.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyanAssembly.lean#L22-L32
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/SmoothJordanMergelyanAssembly.lean#L22-L32

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyan
import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
set_option autoImplicit false
open Complex Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem crouzeix_palencia_of_strictNestedSmoothJordanExhaustion
    (A : E →L[ℂ] E)
    (Omega : StrictNestedSmoothJordanExhaustion
      (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
