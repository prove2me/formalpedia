-- Prove2me | Theorems.Thm_resolvent_mul_aeval_eq_eval_mul_resolvent_sub_aeval_divByMonic
-- name    : resolvent_mul_aeval_eq_eval_mul_resolvent_sub_aeval_divByMonic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:34.954284+00:00
-- url     : https://prove2.me/theorems/672261b6-65b9-4166-9202-73ae18064f69
-- title:
--   resolvent mul aeval eq eval mul resolvent sub aeval div By Monic: resolvent mul aeval eq eval mul resolvent sub aeval div By Monic
-- statement:
--   Splitting `p` by `X - z` inside the resolvent: for `z` in the resolvent
--   set, `R_A(z) p(A) = p(z) R_A(z) - (p /ₘ (X - z))(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L59-L81
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L59-L81

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

theorem resolvent_mul_aeval_eq_eval_mul_resolvent_sub_aeval_divByMonic
    (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    resolvent A z * Polynomial.aeval A p =
      Polynomial.eval z p • resolvent A z -
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)) := by sorry
