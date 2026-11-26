-- Prove2me | Theorems.Thm_continuous_aeval_divByMonic_X_sub_C
-- name    : continuous_aeval_divByMonic_X_sub_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:56.776259+00:00
-- url     : https://prove2.me/theorems/99554a0a-ee16-4e7d-9d3f-cab76f9f1946
-- title:
--   continuous aeval div By Monic X sub C: continuous aeval div By Monic X sub C
-- statement:
--   The operator evaluation of the divided difference
--   `p /ₘ (X - C z)` depends continuously on `z`.
--
--   This is not an immediate application of continuity of polynomial evaluation,
--   because the polynomial itself varies with `z`.  Expanding every coefficient
--   of the quotient as a finite polynomial sum in `z` makes continuity explicit.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L61-L79
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L61-L79

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem continuous_aeval_divByMonic_X_sub_C
    (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    Continuous (fun z : ℂ =>
      Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z))) := by sorry
