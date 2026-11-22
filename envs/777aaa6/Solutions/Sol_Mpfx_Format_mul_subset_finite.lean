-- Prove2me | solution 1 for Mpfx.Format.mul_subset_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:53.514539+00:00
-- url     : https://prove2.me/submissions/0c5bf6ce-576b-499f-a9fb-f0875aa3ee3a

import Definitions.Def_Mpfx_Format_Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Nat.Log
import Definitions.Def_Mpfx_Format_Inference
import Theorems.Thm_Mpfx_Format_mem_toSet
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
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mul
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_mul
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
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

set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise
namespace Mpfx.Format
theorem _root_.solution (F₁ F₂ : Format) :
    F₁.toSet * F₂.toSet ⊆ (opMul F₁ F₂).toSet := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have h_prec := Dyadic.precisionAtMost_mul (mem_toSet.mp hx).1 (mem_toSet.mp hy).1
  have h_quant := Dyadic.quantumAtLeast_mul (mem_toSet.mp hx).2.1 (mem_toSet.mp hy).2.1
  refine ⟨h_prec, h_quant, ?_⟩
  change boundOK
      (match F₁.b, F₂.b with
        | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) => _
        | _, _ => ⊤) (x * y)
  obtain ⟨_, _, hbx⟩ := mem_toSet.mp hx
  obtain ⟨_, _, hby⟩ := mem_toSet.mp hy
  cases hF1_b : F₁.b using Bound.recTopCoe with
  | top => trivial
  | coe b₁ =>
    cases hF2_b : F₂.b using Bound.recTopCoe with
    | top => trivial
    | coe b₂ =>
      rw [hF1_b] at hbx
      rw [hF2_b] at hby
      change |(x : ℚ)| ≤ ((b₁.1 : Dyadic) : ℚ) at hbx
      change |(y : ℚ)| ≤ ((b₂.1 : Dyadic) : ℚ) at hby
      change |((x * y : Dyadic) : ℚ)| ≤ ((b₁.1 * b₂.1 : Dyadic) : ℚ)
      push_cast
      rw [abs_mul]
      have hb1_nn : 0 ≤ ((b₁.1 : Dyadic) : ℚ) := b₁.2
      exact mul_le_mul hbx hby (abs_nonneg _) hb1_nn
end Mpfx.Format
