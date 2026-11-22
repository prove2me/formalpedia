-- Prove2me | solution 1 for Mpfx.Format.abs_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:02:44.316832+00:00
-- url     : https://prove2.me/submissions/7470c2dc-a716-490e-af3f-451b470fa2ff

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
import Theorems.Thm_Mpfx_Format_mem_toSet
import Theorems.Thm_Mpfx_WithSpecial_finite_mul_finite
import Theorems.Thm_Mpfx_WithSpecial_nan_mul
import Theorems.Thm_Mpfx_WithSpecial_mul_nan
import Theorems.Thm_Mpfx_WithSpecial_inf_mul_inf
import Theorems.Thm_Mpfx_WithSpecial_inf_mul_finite
import Theorems.Thm_Mpfx_WithSpecial_finite_mul_inf
import Theorems.Thm_Mpfx_WithSpecial_finite_add_finite
import Theorems.Thm_Mpfx_WithSpecial_nan_add
import Theorems.Thm_Mpfx_WithSpecial_add_nan
import Theorems.Thm_Mpfx_WithSpecial_inf_add_inf
import Theorems.Thm_Mpfx_WithSpecial_inf_add_finite
import Theorems.Thm_Mpfx_WithSpecial_finite_add_inf
import Theorems.Thm_Mpfx_WithSpecial_neg_def
import Theorems.Thm_Mpfx_Format_special_mem_opAbs_iff
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_abs_mem
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
attribute [local simp] Mpfx.Dyadic.coe_abs
attribute [local simp] Mpfx.Dyadic.coe_half
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_rat_abs
attribute [local simp] Mpfx.Dyadic.coe_rat_half
attribute [local simp] Mpfx.Dyadic.coe_rat_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_add
attribute [local simp] Mpfx.Dyadic.coe_real_inj
attribute [local simp] Mpfx.Dyadic.coe_real_mul
attribute [local simp] Mpfx.Dyadic.coe_real_neg
attribute [local simp] Mpfx.Dyadic.coe_real_sub
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.Dyadic.precisionAtMost_neg_iff
attribute [local simp] Mpfx.Dyadic.precisionAtMost_top
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_bot
attribute [local simp] Mpfx.Dyadic.quantumAtLeast_neg_iff
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_p
attribute [local simp] Mpfx.FiniteFormat.unbounded_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_unbounded
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special


attribute [local simp] Mpfx.Format.mem_toSet
attribute [local simp] Mpfx.WithSpecial.finite_mul_finite
attribute [local simp] Mpfx.WithSpecial.nan_mul
attribute [local simp] Mpfx.WithSpecial.mul_nan
attribute [local simp] Mpfx.WithSpecial.inf_mul_inf
attribute [local simp] Mpfx.WithSpecial.inf_mul_finite
attribute [local simp] Mpfx.WithSpecial.finite_mul_inf
attribute [local simp] Mpfx.WithSpecial.finite_add_finite
attribute [local simp] Mpfx.WithSpecial.nan_add
attribute [local simp] Mpfx.WithSpecial.add_nan
attribute [local simp] Mpfx.WithSpecial.inf_add_inf
attribute [local simp] Mpfx.WithSpecial.inf_add_finite
attribute [local simp] Mpfx.WithSpecial.finite_add_inf
attribute [local simp] Mpfx.WithSpecial.neg_def

set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise
namespace Mpfx.Format
theorem _root_.solution (F : Format) :
    WithSpecial.abs '' F.values ⊆ (opAbs F).values := by
  rintro w ⟨u, hu, rfl⟩
  cases h : WithSpecial.abs u with
  | finite z =>
    rcases u with x | (_ | _) <;> simp only [WithSpecial.abs, WithSpecial.finite.injEq,
      reduceCtorEq] at h
    subst h
    exact abs_mem (F := F) hu
  | special s => exact special_mem_opAbs_iff.mpr ⟨u, hu, h⟩
end Mpfx.Format
