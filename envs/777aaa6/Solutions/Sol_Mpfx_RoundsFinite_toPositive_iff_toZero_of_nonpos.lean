-- Prove2me | solution 1 for Mpfx.RoundsFinite.toPositive_iff_toZero_of_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:08:22.835693+00:00
-- url     : https://prove2.me/submissions/705ba47e-a2ea-4620-af9b-6976fdefea77

import Definitions.Def_Mpfx_Rounding_Defs
import Definitions.Def_Mpfx_Format_CanonicalExp
import Definitions.Def_Mpfx_Rounding_Parity
import Definitions.Def_Mpfx_Rounding_Basic
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



set_option autoImplicit true
open Mpfx
namespace Mpfx
namespace RoundsFinite
theorem _root_.solution
    (F : FiniteFormat) {x : ℝ} (hx : x ≤ 0) (y : Dyadic) :
    RoundsFinite F .toPositive x y ↔ RoundsFinite F .toZero x y := by
  unfold RoundsFinite
  refine and_congr_right' ?_
  -- For `x ≤ 0`, a same-signed value at most `|x|` in magnitude lies in `[x, 0]`.
  have key : ∀ z : ℝ, (|z| ≤ |x| ∧ z * x ≥ 0) ↔ (x ≤ z ∧ z ≤ 0) := fun z => by
    rw [abs_of_nonpos hx]
    constructor
    · rintro ⟨h1, h2⟩
      rcases hx.lt_or_eq with hx' | rfl
      · have hz : z ≤ 0 := nonpos_of_mul_nonneg_left h2 hx'
        rw [abs_of_nonpos hz] at h1
        exact ⟨by linarith, hz⟩
      · have : z = 0 := by simpa using h1
        exact ⟨this.ge, this.le⟩
    · rintro ⟨h1, h2⟩
      rw [abs_of_nonpos h2]
      exact ⟨by linarith, mul_nonneg_of_nonpos_of_nonpos h2 hx⟩
  have habs : ∀ {a b : ℝ}, a ≤ 0 → b ≤ 0 → (|a| ≤ |b| ↔ b ≤ a) := fun ha hb => by
    rw [abs_of_nonpos ha, abs_of_nonpos hb, neg_le_neg_iff]
  constructor
  · rintro ⟨hxy, hmin⟩
    have hy0 : (y : ℝ) ≤ 0 := by simpa using hmin 0 (FiniteFormat.zero_mem F) (by simpa using hx)
    obtain ⟨h1, h2⟩ := (key y).mpr ⟨hxy, hy0⟩
    exact ⟨h1, h2, fun z hz h1 h2 => by
      obtain ⟨hxz, hz0⟩ := (key z).mp ⟨h1, h2⟩
      exact (habs hz0 hy0).mpr (hmin z hz hxz)⟩
  · rintro ⟨h1, h2, hmax⟩
    obtain ⟨hxy, hy0⟩ := (key y).mp ⟨h1, h2⟩
    refine ⟨hxy, fun z hz hxz => ?_⟩
    rcases le_or_gt (z : ℝ) 0 with hz0 | hz0
    · obtain ⟨h1, h2⟩ := (key z).mpr ⟨hxz, hz0⟩
      exact (habs hz0 hy0).mp (hmax z hz h1 h2)
    · linarith
end RoundsFinite
end Mpfx
