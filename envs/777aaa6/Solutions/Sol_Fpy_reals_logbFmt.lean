-- Prove2me | solution 1 for Fpy.reals_logbFmt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:27:51.840211+00:00
-- url     : https://prove2.me/submissions/5715f49a-c485-4369-b621-5e4d64bc3392

import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_Format_Inference
import Definitions.Def_Fpy_FormatInference_Ops
import Theorems.Thm_Fpy_Dyadic_coe_real_eq_zero
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
import Theorems.Thm_Mpfx_Dyadic_le_log_of_quantum
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_mono
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_neg_iff
import Theorems.Thm_Mpfx_Dyadic_precisionAtMost_top
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_bot
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
import Theorems.Thm_Mpfx_Format_boundAfterNext_top
import Theorems.Thm_Mpfx_Format_boundOK_neg_iff
import Theorems.Thm_Mpfx_Format_boundOK_zero
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_mem_toSet
import Theorems.Thm_Mpfx_Format_precisionAtMost_bitsFor
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
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
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
    Num.logb u ∈ (logbFmt F).γ := by
  unfold logbFmt
  split
  · next e b he hb =>
    split
    · next hbpos =>
      obtain ⟨w, hw, rfl⟩ := hu
      rcases w with d | (a | _)
      · simp only [WithSpecial.toReal_finite, Num.logb, Dyadic.coe_real_eq_zero]
        split
        · exact ⟨.special (.inf true), trivial, rfl⟩
        · next hd0 =>
          have hd0' : (d : ℝ) ≠ 0 := fun h => hd0 (eq_zero_of_coe_real_zero h)
          set k := Int.log 2 |(d : ℝ)|
          refine ⟨.finite (Dyadic.ofIntZpow k 0), ?_, by simp⟩
          obtain ⟨_, hq, hbd⟩ := hw
          rw [he] at hq
          rw [hb] at hbd
          change |(d : ℚ)| ≤ ((b.1 : Mpfx.Dyadic) : ℚ) at hbd
          have hbdR : |(d : ℝ)| ≤ ((b.1 : Mpfx.Dyadic) : ℝ) := by exact_mod_cast hbd
          have hlo : e ≤ k := Dyadic.le_log_of_quantum hq hd0'
          have hhi : k ≤ Int.log 2 ((b.1 : Mpfx.Dyadic) : ℝ) :=
            Int.log_mono_right (abs_pos.mpr hd0') hbdR
          set L := Int.log 2 ((b.1 : Mpfx.Dyadic) : ℝ)
          have hkZ : |k| ≤ ((max e.natAbs L.natAbs : ℕ) : ℤ) := by
            push_cast
            rw [abs_le]
            have h1 := neg_abs_le e
            have h2 := le_abs_self L
            have h3 := le_max_left |e| |L|
            have h4 := le_max_right |e| |L|
            constructor <;> linarith
          have hk : |(k : ℝ)| ≤ (((max e.natAbs L.natAbs : ℕ) : ℤ) : ℝ) := by
            rw [← Int.cast_abs]
            exact Int.cast_le.mpr hkZ
          refine ⟨Dyadic.precisionAtMost_mono le_sup_right
            (Format.precisionAtMost_bitsFor (Dyadic.quantumAtLeast_ofIntZpow le_rfl)
              (by simpa using hk)), Dyadic.quantumAtLeast_ofIntZpow le_rfl, ?_⟩
          change |((Dyadic.ofIntZpow k 0 : Mpfx.Dyadic) : ℚ)| ≤
            ((Dyadic.ofIntZpow _ 0 : Mpfx.Dyadic) : ℚ)
          simp only [Dyadic.coe_rat_ofIntZpow, zpow_zero, mul_one]
          rw [← Int.cast_abs]
          exact Int.cast_le.mpr hkZ
      · exact ⟨.special (.inf false), ⟨a, hw⟩, rfl⟩
      · exact ⟨.special .nan, hw, rfl⟩
    · trivial
  · trivial
end Fpy
