-- Prove2me | Theorems.Thm_aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic
-- name    : aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:37:15.601861+00:00
-- url     : https://prove2.me/theorems/2e274330-4e48-48ad-a737-3300f2a6936c
-- title:
--   aeval mul resolvent eq eval mul resolvent sub aeval div By Monic: aeval mul resolvent eq eval mul resolvent sub aeval div By Monic
-- statement:
--   The right-oriented resolvent splitting used directly in `p(A) G`:
--   `p(A) R_A(z) = p(z) R_A(z) - (p /ₘ (X - z))(A)`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L85-L108
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L85-L108

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

theorem aeval_mul_resolvent_eq_eval_mul_resolvent_sub_aeval_divByMonic
    (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    Polynomial.aeval A p * resolvent A z =
      Polynomial.eval z p • resolvent A z -
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)) := by sorry
