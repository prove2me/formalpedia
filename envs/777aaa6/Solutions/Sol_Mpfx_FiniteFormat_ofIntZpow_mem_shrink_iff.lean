-- Prove2me | solution 1 for Mpfx.FiniteFormat.ofIntZpow_mem_shrink_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:09:47.891183+00:00
-- url     : https://prove2.me/submissions/5dd510a9-5da5-4908-a89f-59f446ab69c8

import Definitions.Def_Mpfx_Format_Next
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Format_Parity
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow_ne_zero
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_shrink
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_p_pos
import Theorems.Thm_Mpfx_FiniteFormat_shrink_exp_bot
import Theorems.Thm_Mpfx_FiniteFormat_shrink_exp_coe
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_special_mem_values
import Theorems.Thm_Mpfx_Format_unbounded_b
import Theorems.Thm_Mpfx_Format_unbounded_exp
import Theorems.Thm_Mpfx_Format_unbounded_p
import Theorems.Thm_Mpfx_Format_unbounded_specials
import Theorems.Thm_Mpfx_Format_unbounded_unbounded
import Theorems.Thm_Mpfx_Format_withBound_b
import Theorems.Thm_Mpfx_Format_withBound_exp
import Theorems.Thm_Mpfx_Format_withBound_p
import Theorems.Thm_Mpfx_Format_withBound_specials
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_coeff_eq_of_shift
import Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded
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
attribute [local simp] Mpfx.FiniteFormat.extend_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_p
attribute [local simp] Mpfx.FiniteFormat.unbounded_toFormat
attribute [local simp] Mpfx.FiniteFormat.unbounded_unbounded
attribute [local simp] Mpfx.Format.boundAfterNext_top
attribute [local simp] Mpfx.Format.boundOK_neg_iff
attribute [local simp] Mpfx.Format.boundOK_zero
attribute [local simp] Mpfx.Format.finite_mem_values
attribute [local simp] Mpfx.Format.special_mem_values
attribute [local simp] Mpfx.Format.unbounded_b
attribute [local simp] Mpfx.Format.unbounded_exp
attribute [local simp] Mpfx.Format.unbounded_p
attribute [local simp] Mpfx.Format.unbounded_specials
attribute [local simp] Mpfx.Format.unbounded_unbounded
attribute [local simp] Mpfx.Format.withBound_b
attribute [local simp] Mpfx.Format.withBound_exp
attribute [local simp] Mpfx.Format.withBound_p
attribute [local simp] Mpfx.Format.withBound_specials
attribute [local simp] Mpfx.Special.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special


attribute [local simp] Mpfx.FiniteFormat.IsOdd.neg_iff
attribute [local simp] Mpfx.FiniteFormat.isEven_zero
attribute [local simp] Mpfx.FiniteFormat.IsEven.neg_iff

set_option autoImplicit true
open Mpfx
open Mpfx.FiniteFormat
namespace Mpfx.FiniteFormat
theorem _root_.solution (F : FiniteFormat) (h : F.p ≠ ((1 : ℕ) : Prec))
    {k e : ℤ} (he : F.exp ≤ (e : QExp)) (hk : ∀ p : ℕ, F.p = p → |k| ≤ 2 ^ p)
    (hce : k ≠ 0 → e ≤ F.canonicalExp (Dyadic.ofIntZpow k e)) :
    Dyadic.ofIntZpow k e ∈ (F.shrink h).unbounded ↔ Even k := by
  constructor
  · intro hmem
    by_contra hodd
    have hk0 : k ≠ 0 := by rintro rfl; exact hodd Even.zero
    have hkc := hce hk0
    obtain ⟨m, hm⟩ := (F.shrink h).exists_mul_zpow_canonicalExp hmem
    rw [canonicalExp_shrink F h (Dyadic.coe_ofIntZpow_ne_zero hk0 e)] at hm
    -- `k · 2^e = m · 2^(c + 1)` with `e < c + 1` makes `k` even.
    have hshift := coeff_eq_of_shift (K := ℝ) (by omega) ((Dyadic.coe_ofIntZpow k e).symm.trans hm)
    exact hodd (hshift ▸ (Int.even_pow.mpr ⟨even_two, by omega⟩).mul_left m)
  · rintro ⟨j, rfl⟩
    have hd : Dyadic.ofIntZpow (j + j) e = Dyadic.ofIntZpow j (e + 1) := Dyadic.ext_real (by
      simp only [Dyadic.coe_ofIntZpow]; rw [zpow_add_one₀ two_ne_zero]; push_cast; ring)
    rw [hd]
    refine ofIntZpow_mem_unbounded _ (fun {e'} he' => ?_) (fun {p} hp => ?_)
    · cases hexp : F.exp using QExp.recBotCoe with
      | bot => rw [shrink_exp_bot h hexp] at he'; exact absurd he' WithBot.bot_ne_coe
      | coe e₀ =>
        rw [shrink_exp_coe h hexp] at he'
        rw [hexp] at he
        have h1 := WithBot.coe_inj.mp he'
        have h2 := WithBot.coe_le_coe.mp he
        omega
    · change F.p - 1 = _ at hp
      cases hF : F.p using ENat.recTopCoe with
      | top => rw [hF] at hp; exact absurd hp (ENat.top_ne_coe p)
      | coe n =>
        rw [hF] at hp
        have h1 : n ≠ 1 := fun h1 => h (by rw [hF, h1])
        have hn : n = p + 1 := by
          have : n - 1 = p := ENat.coe_inj.mp hp
          have := F.p_pos hF
          omega
        have := hk n hF
        rw [hn, pow_succ, ← two_mul, abs_mul, abs_two] at this
        linarith
end Mpfx.FiniteFormat
