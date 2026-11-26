-- Prove2me | Theorems.Thm_commute_aeval_resolvent
-- name    : commute_aeval_resolvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:34.117245+00:00
-- url     : https://prove2.me/theorems/b899e28e-ac51-5926-b806-e9e1f57297c7
-- title:
--   commute aeval resolvent: commute aeval resolvent
-- statement:
--   Polynomial evaluation at `A` commutes with the resolvent of `A`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L122-L127
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L122-L127

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem commute_aeval_resolvent (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ resolventSet ℂ A) : Commute (Polynomial.aeval A p) (resolvent A z) := by sorry
