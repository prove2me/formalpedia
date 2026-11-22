-- Prove2me | solution 1 for Mpfx.exists_mem_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:35:39.754484+00:00
-- url     : https://prove2.me/submissions/b31fce00-bd07-4041-b27b-ae5b3204a4ac

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
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
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_format_next_eq
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
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
import Theorems.Thm_Mpfx_IsFaithfulRound_mul_nonneg
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_coe_real_ofIntZpow_one
import Theorems.Thm_Mpfx_floor_mantissa_lt
import Theorems.Thm_Mpfx_mul_zpow_neg_self
import Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded
import Theorems.Thm_Mpfx_precisionAtMost_one_zpow
import Theorems.Thm_Mpfx_rnd_special
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
attribute [local simp] Mpfx.FiniteFormat.IsEven.neg_iff
attribute [local simp] Mpfx.FiniteFormat.IsOdd.neg_iff
attribute [local simp] Mpfx.FiniteFormat.extend_toFormat
attribute [local simp] Mpfx.FiniteFormat.isEven_zero
attribute [local simp] Mpfx.FiniteFormat.unbounded_b
attribute [local simp] Mpfx.FiniteFormat.unbounded_canonicalExp
attribute [local simp] Mpfx.FiniteFormat.unbounded_exp
attribute [local simp] Mpfx.FiniteFormat.unbounded_isUndefined
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
attribute [local simp] Mpfx.rnd_special



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F : FiniteFormat} {b : Dyadic} (hb : 0 ≤ (b : ℝ)) :
    ∃ N : Dyadic, N ∈ F.unbounded ∧ (b : ℝ) < N ∧ (N : ℝ) ≤ F.toFormat.next b := by
  by_cases hg : F.exp = ⊥ → 0 < (b : ℝ)
  swap
  · -- No minimum quantum and `b = 0`: take `1 = next 0`.
    push Not at hg
    obtain ⟨hexp, hb0⟩ := hg
    obtain rfl : b = 0 := Dyadic.ext_real (by rw [Dyadic.coe_real_zero]; linarith)
    have hnext : F.toFormat.next 0 = Dyadic.ofIntZpow 1 0 := by
      unfold Format.next
      rw [hexp]
      cases hp : F.p using ENat.recTopCoe with
      | top => exact (F.finite.elim (· hp) (· hexp)).elim
      | coe p => exact Dyadic.ext_real (by simp)
    refine ⟨Dyadic.ofIntZpow 1 0, ⟨precisionAtMost_one_zpow F.pos 0, by
      change Dyadic.quantumAtLeast F.exp _; rw [hexp]; trivial, trivial⟩, ?_, ?_⟩
    · rw [coe_real_ofIntZpow_one, Dyadic.coe_real_zero]; norm_num
    · rw [hnext]
  set c := F.canonicalExp (b : ℝ)
  set s := (b : ℝ) * 2 ^ (-c)
  have h2c : (0 : ℝ) < 2 ^ c := zpow_pos two_pos c
  have hs0 : 0 ≤ s := mul_nonneg hb (zpow_pos two_pos _).le
  have hfl := Int.floor_le s
  have hlt := Int.lt_floor_add_one s
  have hb_eq : s * 2 ^ c = b := mul_zpow_neg_self _ _
  refine ⟨Dyadic.ofIntZpow (⌊s⌋ + 1) c, ofIntZpow_mem_unbounded F
    (fun he => F.exp_le_canonicalExp _ he) (fun {p} hp => ?_), ?_, ?_⟩
  · have h1 := (abs_lt.mp (floor_mantissa_lt (F := F) (x := (b : ℝ)) hp)).2
    have h2 : ⌊s⌋ < 2 ^ p := by exact_mod_cast hfl.trans_lt h1
    have h3 : 0 ≤ ⌊s⌋ := Int.floor_nonneg.mpr hs0
    rw [abs_of_nonneg (by omega)]; omega
  · rw [Dyadic.coe_ofIntZpow, ← hb_eq]; push_cast; nlinarith
  · rw [FiniteFormat.format_next_eq F hb hg, Dyadic.coe_real_add, coe_real_ofIntZpow_one,
      Dyadic.coe_ofIntZpow]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hfl h2c.le]
end Mpfx
