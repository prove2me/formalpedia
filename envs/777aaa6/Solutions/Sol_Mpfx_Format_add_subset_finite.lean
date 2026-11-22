-- Prove2me | solution 1 for Mpfx.Format.add_subset_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:55.148087+00:00
-- url     : https://prove2.me/submissions/e18d44d0-cc83-4234-8ba5-32860234f7c7

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
import Theorems.Thm_Mpfx_Format_precisionAtMost_bitsFor
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
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_add
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_anti
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
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
section
namespace Mpfx
namespace Format
open scoped Pointwise
end Format
namespace WithSpecial
end WithSpecial
namespace Format
open scoped Pointwise
private theorem add_prec_finite {F₁ F₂ : Format} {x y : Dyadic}
    {b1 b2 : NonNegDyadic} {e1 e2 : ℤ}
    (hF1_b : F₁.b = (b1 : Bound)) (hF2_b : F₂.b = (b2 : Bound))
    (hF1_exp : F₁.exp = (e1 : QExp)) (hF2_exp : F₂.exp = (e2 : QExp))
    (hx : x ∈ F₁) (hy : y ∈ F₂) :
    Dyadic.precisionAtMost
      (bitsFor ((b1.1 + b2.1 : Dyadic) : ℝ) (min e1 e2) : Prec)
      (x + y) := by
  obtain ⟨_, hqx, hbx⟩ := hx
  obtain ⟨_, hqy, hby⟩ := hy
  rw [hF1_exp] at hqx
  rw [hF2_exp] at hqy
  rw [hF1_b] at hbx
  rw [hF2_b] at hby
  change |(x : ℚ)| ≤ ((b1.1 : Dyadic) : ℚ) at hbx
  change |(y : ℚ)| ≤ ((b2.1 : Dyadic) : ℚ) at hby
  have hq := Dyadic.quantumAtLeast_add
    (Dyadic.quantumAtLeast_anti (WithBot.coe_le_coe.mpr (min_le_left e1 e2)) hqx)
    (Dyadic.quantumAtLeast_anti (WithBot.coe_le_coe.mpr (min_le_right e1 e2)) hqy)
  refine precisionAtMost_bitsFor hq ?_
  have hbxR : |(x : ℝ)| ≤ ((b1.1 : Dyadic) : ℝ) := by exact_mod_cast hbx
  have hbyR : |(y : ℝ)| ≤ ((b2.1 : Dyadic) : ℝ) := by exact_mod_cast hby
  rw [Dyadic.coe_real_add, Dyadic.coe_real_add]
  exact (abs_add_le _ _).trans (add_le_add hbxR hbyR)
end Format
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Format
open scoped Pointwise
namespace Mpfx.Format
theorem _root_.solution (F₁ F₂ : Format) :
    F₁.toSet + F₂.toSet ⊆ (opAdd F₁ F₂).toSet := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have h_quant := Dyadic.quantumAtLeast_add
    (Dyadic.quantumAtLeast_anti (min_le_left _ _) (mem_toSet.mp hx).2.1)
    (Dyadic.quantumAtLeast_anti (min_le_right _ _) (mem_toSet.mp hy).2.1)
  obtain ⟨_, _, hbx⟩ := mem_toSet.mp hx
  obtain ⟨_, _, hby⟩ := mem_toSet.mp hy
  refine ⟨?_, h_quant, ?_⟩
  · change Dyadic.precisionAtMost (opAddPrec F₁ F₂) (x + y)
    unfold opAddPrec
    cases hF1_b : F₁.b using Bound.recTopCoe with
    | top => trivial
    | coe b1 =>
      cases hF2_b : F₂.b using Bound.recTopCoe with
      | top => trivial
      | coe b2 =>
        cases hF1_exp : F₁.exp using QExp.recBotCoe with
        | bot =>
          -- min ≤ ⊥ ⇒ min = ⊥ ⇒ ⊤ branch
          simp only [bot_inf_eq]; trivial
        | coe e1 =>
          cases hF2_exp : F₂.exp using QExp.recBotCoe with
          | bot =>
            simp only [inf_bot_eq]; trivial
          | coe e2 =>
            have h_min_eq : min (e1 : QExp) (e2 : QExp)
                = ((min e1 e2 : ℤ) : QExp) := (WithBot.coe_min e1 e2).symm
            rw [h_min_eq]
            have := add_prec_finite hF1_b hF2_b hF1_exp hF2_exp
              (mem_toSet.mp hx) (mem_toSet.mp hy)
            convert this using 3
  · change boundOK
        (match F₁.b, F₂.b with
          | (b₁ : NonNegDyadic), (b₂ : NonNegDyadic) => _
          | _, _ => ⊤) (x + y)
    cases hF1_b : F₁.b using Bound.recTopCoe with
    | top => trivial
    | coe b1 =>
      cases hF2_b : F₂.b using Bound.recTopCoe with
      | top => trivial
      | coe b2 =>
        rw [hF1_b] at hbx
        rw [hF2_b] at hby
        change |(x : ℚ)| ≤ ((b1.1 : Dyadic) : ℚ) at hbx
        change |(y : ℚ)| ≤ ((b2.1 : Dyadic) : ℚ) at hby
        change |((x + y : Dyadic) : ℚ)| ≤ ((b1.1 + b2.1 : Dyadic) : ℚ)
        push_cast
        calc |(x : ℚ) + (y : ℚ)|
            ≤ |(x : ℚ)| + |(y : ℚ)| := abs_add_le _ _
          _ ≤ ((b1.1 : Dyadic) : ℚ) + ((b2.1 : Dyadic) : ℚ) := add_le_add hbx hby
end Mpfx.Format
