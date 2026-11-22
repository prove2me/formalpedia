-- Prove2me | solution 1 for Mpfx.Format.mem_shrink_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:01:49.745863+00:00
-- url     : https://prove2.me/submissions/f5b2a6ac-7d66-4809-822c-d040a101841a

import Definitions.Def_Mpfx_Format_Defs
import Definitions.Def_Mpfx_Format_Containment
import Theorems.Thm_Mpfx_Format_mem_unbounded_of_le
import Theorems.Thm_Mpfx_Format_containsSub
import Theorems.Thm_Mpfx_Format_subset_iff_contains
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
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


attribute [local simp] Mpfx.FiniteFormat.extend_toFormat
section
namespace Mpfx
namespace Format
end Format
namespace FiniteFormat
end FiniteFormat
namespace Format
end Format
namespace FiniteFormat
end FiniteFormat
namespace Format
private theorem map_add_one_le {a b : QExp} (h : a ≤ b) : a.map (· + 1) ≤ b.map (· + 1) := by
  cases a using QExp.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    cases b using QExp.recBotCoe with
    | bot => exact absurd h (by simp)
    | coe b =>
      exact WithBot.coe_le_coe.mpr (show a + 1 ≤ b + 1 by have := WithBot.coe_le_coe.mp h; omega)
end Format
end Mpfx
end

set_option autoImplicit true
open Mpfx
open Mpfx.Format
namespace Mpfx.Format
theorem _root_.solution {G H : Format} (hsub : G ⊆ H) (hbr : BoundRep G)
    (hnt : G.Nontrivial) (hp : ((2 : ℕ) : Prec) ≤ H.p) {y : Dyadic} (hy : y ∈ G.shrink) :
    y ∈ H.shrink.unbounded := by
  rcases (subset_iff_contains hbr hnt).mp hsub with
    ⟨hpp, he, -, -⟩ | ⟨e₁, p₂, he₁, -, hp₂, hbb, he, -, hs⟩
  · exact mem_unbounded_of_le (tsub_le_tsub_right hpp 1) (map_add_one_le he) hy.1 hy.2.1
  · have h2 : 2 ≤ p₂ := by rw [hp₂] at hp; exact ENat.coe_le_coe.mp hp
    refine containsSub (F₁ := G.shrink) (F₂ := H.shrink.unbounded) (exp₁ := e₁ + 1)
      (p₂ := p₂ - 1) (by change G.exp.map _ = _; rw [he₁]; rfl) (by omega)
      (by change H.p - 1 = _; rw [hp₂]; norm_cast) ?_ (map_add_one_le he) le_top hs y hy
    rw [show e₁ + 1 + ((p₂ - 1 : ℕ) : ℤ) = e₁ + p₂ by omega]
    exact hbb
end Mpfx.Format
