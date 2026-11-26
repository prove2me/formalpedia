-- Prove2me | Theorems.Thm_aeval_mul_smul_resolvent_eq_smul_eval_mul_resolvent_sub_aeval_divByMonic
-- name    : aeval_mul_smul_resolvent_eq_smul_eval_mul_resolvent_sub_aeval_divByMonic
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:37:29.46097+00:00
-- url     : https://prove2.me/theorems/97dba313-cf82-5ee2-9baf-dc9886d61381
-- title:
--   aeval mul smul resolvent eq smul eval mul resolvent sub aeval div By Monic: aeval mul smul resolvent eq smul eval mul resolvent sub aeval div By Monic
-- statement:
--   The right-oriented splitting with a scalar boundary weight `h`, in the
--   pointwise form used before applying contour-integral linearity in L4.2e.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L112-L119
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PalenciaSupport.lean#L112-L119

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

theorem aeval_mul_smul_resolvent_eq_smul_eval_mul_resolvent_sub_aeval_divByMonic
    (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ resolventSet ℂ A) (h : ℂ) :
    Polynomial.aeval A p * (h • resolvent A z) =
      (h * Polynomial.eval z p) • resolvent A z -
        h • Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)) := by sorry
