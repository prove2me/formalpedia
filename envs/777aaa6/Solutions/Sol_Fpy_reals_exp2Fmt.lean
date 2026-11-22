-- Prove2me | solution 1 for Fpy.reals_exp2Fmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:27:52.315237+00:00
-- url     : https://prove2.me/submissions/0eca2822-3314-486d-bd87-a2c72733cf3b

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Mpfx_Dyadic_coe_abs
import Theorems.Thm_Mpfx_Dyadic_coe_half
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_rat_abs
import Theorems.Thm_Mpfx_Dyadic_coe_rat_half
import Theorems.Thm_Mpfx_Dyadic_coe_rat_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_add
import Theorems.Thm_Mpfx_Dyadic_coe_real_eq_ratCast
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_coe_real_mul
import Theorems.Thm_Mpfx_Dyadic_coe_real_neg
import Theorems.Thm_Mpfx_Dyadic_coe_real_sub
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_neg_iff
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_ofIntZpow
import Theorems.Thm_Mpfx_FiniteFormat_IsEven_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_IsOdd_neg_iff
import Theorems.Thm_Mpfx_FiniteFormat_extend_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_isEven_zero
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_b
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_exp
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_p
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_toFormat
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_unbounded
import Theorems.Thm_Mpfx_FiniteFormat_zero_mem
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_mem_toSet
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
import Theorems.Thm_Mpfx_Format_zero_mem
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_add_nan
import Theorems.Thm_Mpfx_WithSpecial_finite_add_finite
import Theorems.Thm_Mpfx_WithSpecial_finite_add_inf
import Theorems.Thm_Mpfx_WithSpecial_finite_mul_finite
import Theorems.Thm_Mpfx_WithSpecial_finite_mul_inf
import Theorems.Thm_Mpfx_WithSpecial_inf_add_finite
import Theorems.Thm_Mpfx_WithSpecial_inf_add_inf
import Theorems.Thm_Mpfx_WithSpecial_inf_mul_finite
import Theorems.Thm_Mpfx_WithSpecial_inf_mul_inf
import Theorems.Thm_Mpfx_WithSpecial_mul_nan
import Theorems.Thm_Mpfx_WithSpecial_nan_add
import Theorems.Thm_Mpfx_WithSpecial_nan_mul
import Theorems.Thm_Mpfx_WithSpecial_neg_def
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
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
attribute [local simp] Mpfx.Format.mem_toSet
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
attribute [local simp] Mpfx.WithSpecial.add_nan
attribute [local simp] Mpfx.WithSpecial.finite_add_finite
attribute [local simp] Mpfx.WithSpecial.finite_add_inf
attribute [local simp] Mpfx.WithSpecial.finite_mul_finite
attribute [local simp] Mpfx.WithSpecial.finite_mul_inf
attribute [local simp] Mpfx.WithSpecial.inf_add_finite
attribute [local simp] Mpfx.WithSpecial.inf_add_inf
attribute [local simp] Mpfx.WithSpecial.inf_mul_finite
attribute [local simp] Mpfx.WithSpecial.inf_mul_inf
attribute [local simp] Mpfx.WithSpecial.mul_nan
attribute [local simp] Mpfx.WithSpecial.nan_add
attribute [local simp] Mpfx.WithSpecial.nan_mul
attribute [local simp] Mpfx.WithSpecial.neg_def
attribute [local simp] Mpfx.WithSpecial.neg_finite
attribute [local simp] Mpfx.WithSpecial.neg_neg
attribute [local simp] Mpfx.WithSpecial.neg_special
attribute [local simp] Mpfx.WithSpecial.toReal_finite
attribute [local simp] Mpfx.WithSpecial.toReal_special
attribute [local simp] Mpfx.rnd_special



set_option autoImplicit true
open Fpy
open Mpfx
namespace Fpy
theorem _root_.solution {F : Format} {u : Num} (hu : u ∈ F.reals) :
    Num.exp2 u ∈ (exp2Fmt F).γ := by
  unfold exp2Fmt
  split
  · next e b he hb =>
    split
    · next he0 =>
      obtain ⟨w, hw, rfl⟩ := hu
      rcases w with d | (a | _)
      · obtain ⟨_, hq, hbd⟩ := hw
        rw [he] at hq
        rw [hb] at hbd
        change |(d : ℚ)| ≤ ((b.1 : Mpfx.Dyadic) : ℚ) at hbd
        obtain ⟨c, hc⟩ := (Dyadic.quantumAtLeast_coe e d).mp hq
        obtain ⟨k, hdk⟩ : ∃ k : ℤ, (d : ℚ) = k :=
          ⟨c * 2 ^ e.toNat, by rw [hc]; push_cast; rw [← zpow_natCast, Int.toNat_of_nonneg he0]⟩
        set B := ⌊((b.1 : Mpfx.Dyadic) : ℚ)⌋
        have hkB : |k| ≤ B := by
          refine Int.le_floor.mpr ?_
          rw [Int.cast_abs, ← hdk]
          exact hbd
        refine ⟨.finite (Dyadic.ofIntZpow 1 k), ⟨?_, ?_, ?_⟩, ?_⟩
        · exact ⟨1, k, by rw [Dyadic.coe_rat_ofIntZpow], by norm_num⟩
        · exact Dyadic.quantumAtLeast_ofIntZpow (WithBot.coe_le_coe.mpr (by
            have := neg_abs_le k
            omega))
        · change |((Dyadic.ofIntZpow 1 k : Mpfx.Dyadic) : ℚ)| ≤
            ((Dyadic.ofIntZpow 1 B : Mpfx.Dyadic) : ℚ)
          simp only [Dyadic.coe_rat_ofIntZpow, Int.cast_one, one_mul]
          rw [abs_of_pos (zpow_pos (by norm_num) _)]
          exact zpow_le_zpow_right₀ (by norm_num) ((le_abs_self k).trans hkB)
        · have hdR : (d : ℝ) = k := by
            rw [Dyadic.coe_real_eq_ratCast, hdk]
            push_cast
            rfl
          simp only [WithSpecial.toReal_finite, Num.exp2, hdR, Real.rpow_intCast,
            Dyadic.coe_ofIntZpow, Int.cast_one, one_mul]
      · rcases a with _ | _
        · exact ⟨.special (.inf false), hw, rfl⟩
        · exact ⟨.finite 0, Format.zero_mem _, by simp [Num.exp2]⟩
      · exact ⟨.special .nan, hw, rfl⟩
    · trivial
  · trivial
end Fpy
