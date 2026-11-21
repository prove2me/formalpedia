-- Prove2me | solution 1 for Mpfx.Format.containsSub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:54:44.384346+00:00
-- url     : https://prove2.me/submissions/f8b438f2-a078-4af7-8637-c98cb647d60a

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Format_boundOK_mono
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
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_of_abs_le
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_anti
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe
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



set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {F₁ F₂ : Format}
    {exp₁ : ℤ} (he₁ : F₁.exp = (exp₁ : QExp))
    {p₂ : ℕ} (hp₂pos : 0 < p₂) (hp₂ : F₂.p = (p₂ : Prec))
    (hbprec : F₁.b ≤ ((nnPow (exp₁ + (p₂ : ℤ)) : NonNegDyadic) : Bound))
    (he : F₂.exp ≤ F₁.exp)
    (hb : F₁.b ≤ F₂.b) (hs : F₁.specials ⊆ F₂.specials) :
    F₁ ⊆ F₂ := by
  refine ⟨fun x hx => ?_, hs⟩
  obtain ⟨_, hex, hbx⟩ := hx
  -- x = c · 2^exp₁.
  have hex_coe : Dyadic.quantumAtLeast (exp₁ : QExp) x := by rw [← he₁]; exact hex
  obtain ⟨c, hx_eq⟩ := (Dyadic.quantumAtLeast_coe exp₁ x).mp hex_coe
  -- |x| ≤ 2^(exp₁ + p₂), from the bound on F₁.b.
  have hbx' : |(x : ℚ)| ≤ (2 : ℚ) ^ (exp₁ + (p₂ : ℤ)) := by
    have h_bnd := boundOK_mono hbprec hbx
    rw [show boundOK _ x = (|(x : ℚ)| ≤ ((nnPow (exp₁ + (p₂ : ℤ))).val : ℚ)) from rfl] at h_bnd
    rwa [coe_nnPow] at h_bnd
  -- |c| ≤ 2^p₂.
  have h2exp_pos : (0 : ℚ) < (2 : ℚ) ^ exp₁ := zpow_pos (by norm_num) _
  have hc_le_rat : |(c : ℚ)| ≤ (2 : ℚ) ^ (p₂ : ℤ) := by
    have h1 : |(c : ℚ)| * (2 : ℚ) ^ exp₁ ≤ (2 : ℚ) ^ (exp₁ + (p₂ : ℤ)) := by
      calc |(c : ℚ)| * (2 : ℚ) ^ exp₁
          = |(c : ℚ) * (2 : ℚ) ^ exp₁| := by
            rw [abs_mul, abs_of_pos h2exp_pos]
        _ = |(x : ℚ)| := by rw [hx_eq]
        _ ≤ (2 : ℚ) ^ (exp₁ + (p₂ : ℤ)) := hbx'
    have h2 : (2 : ℚ) ^ (exp₁ + (p₂ : ℤ)) = (2 : ℚ) ^ (p₂ : ℤ) * (2 : ℚ) ^ exp₁ := by
      rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]; ring
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 h2exp_pos
  have hc_le : |c| ≤ (2 : ℤ) ^ p₂ := by
    have : ((|c| : ℤ) : ℚ) ≤ (((2 : ℤ) ^ p₂ : ℤ) : ℚ) := by
      rw [Int.cast_abs]; push_cast
      simp only [← zpow_natCast (2 : ℚ) p₂]
      exact hc_le_rat
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · rw [hp₂]; exact Dyadic.precisionAtMost_of_abs_le hp₂pos c exp₁ hx_eq hc_le
  · exact Dyadic.quantumAtLeast_anti he hex
  · exact boundOK_mono hb hbx
end Mpfx.Format
