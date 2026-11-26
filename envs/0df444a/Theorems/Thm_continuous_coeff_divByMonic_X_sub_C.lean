-- Prove2me | Theorems.Thm_continuous_coeff_divByMonic_X_sub_C
-- name    : continuous_coeff_divByMonic_X_sub_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:40:34.006829+00:00
-- url     : https://prove2.me/theorems/836c3521-9de1-434b-91a6-e91f6aaa9363
-- title:
--   continuous coeff div By Monic X sub C: continuous coeff div By Monic X sub C
-- statement:
--   Every coefficient of the polynomial divided difference depends
--   continuously on its boundary point.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L83-L93
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ProductContour.lean#L83-L93

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Mathlib.Topology.Algebra.Polynomial
import Definitions.Def_Operator_Crouzeix_ProductContour
set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem continuous_coeff_divByMonic_X_sub_C (p : Polynomial ℂ) (n : ℕ) :
    Continuous (fun z : ℂ =>
      (p /ₘ (Polynomial.X - Polynomial.C z)).coeff n) := by sorry
