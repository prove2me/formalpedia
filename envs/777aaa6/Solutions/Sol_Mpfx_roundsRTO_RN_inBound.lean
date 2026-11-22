-- Prove2me | solution 1 for Mpfx.roundsRTO_RN_inBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:39:50.14226+00:00
-- url     : https://prove2.me/submissions/1d023695-7315-4485-8c0e-9cb7d1e562b7

import Definitions.Def_Mpfx_DoubleRounding_Nearest
import Definitions.Def_Mpfx_Rounding_Restrict
import Definitions.Def_Mpfx_DoubleRounding_Total
import Theorems.Thm_Mpfx_LocalDoubleRounding_inBound
import Theorems.Thm_Mpfx_eq_of_rule
import Theorems.Thm_Mpfx_withBound_subset_of_boundOK
import Theorems.Thm_Mpfx_abs_le_mid_of_nearest
import Theorems.Thm_Mpfx_abs_le_of_nearest_of_abs_lt_mid
import Theorems.Thm_Mpfx_abs_ne_of_toOdd
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
import Theorems.Thm_Mpfx_FiniteFormat_neg_mem
import Theorems.Thm_Mpfx_FiniteFormat_subset_unbounded
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
import Theorems.Thm_Mpfx_Format_extend_mono
import Theorems.Thm_Mpfx_Format_finite_mem_values
import Theorems.Thm_Mpfx_Format_neg_mem
import Theorems.Thm_Mpfx_Format_self_subset_extend
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
import Theorems.Thm_Mpfx_RoundsFinite_unique
import Theorems.Thm_Mpfx_Special_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_finite
import Theorems.Thm_Mpfx_WithSpecial_neg_neg
import Theorems.Thm_Mpfx_WithSpecial_neg_special
import Theorems.Thm_Mpfx_WithSpecial_toReal_finite
import Theorems.Thm_Mpfx_WithSpecial_toReal_special
import Theorems.Thm_Mpfx_abs_coe_real_le_of_boundOK
import Theorems.Thm_Mpfx_abs_faithful_le_of_le
import Theorems.Thm_Mpfx_boundOK_boundAfterNext_next
import Theorems.Thm_Mpfx_boundOK_boundAfterNext_of_boundOK
import Theorems.Thm_Mpfx_boundOK_coe_of_abs_le
import Theorems.Thm_Mpfx_boundOK_of_abs_le
import Theorems.Thm_Mpfx_bound_top_of_withBound_top_subset
import Theorems.Thm_Mpfx_eq_zero_of_coe_real_zero
import Theorems.Thm_Mpfx_le_abs_faithful_of_le
import Theorems.Thm_Mpfx_mem_unbounded_of_mem
import Theorems.Thm_Mpfx_next_mono
import Theorems.Thm_Mpfx_nonneg_coe_real
import Theorems.Thm_Mpfx_not_isUndefined_of_two_le_p
import Theorems.Thm_Mpfx_not_isUndefined_toNegative
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
import Theorems.Thm_Mpfx_rnd_special
import Theorems.Thm_Mpfx_roundsRTO_RN_finite
import Theorems.Thm_Mpfx_roundsRTO_RN_finite_of_extend
import Theorems.Thm_Mpfx_two_le_p_of_nontrivial_extend_two
import Theorems.Thm_P2M_Mpfx_next_mem_unbounded__2b8c4e4daa3e
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


section
namespace Mpfx
private theorem exists_floor {F : FiniteFormat} {b : NonNegDyadic} (hFb : F.b = (b : Bound)) :
    ∃ d : Dyadic, d ∈ F.unbounded ∧ 0 ≤ (d : ℝ) ∧ (d : ℝ) ≤ b.val ∧
      ∀ v ∈ F.unbounded, Format.boundOK F.b v → |(v : ℝ)| ≤ d := by
  have hb := nonneg_coe_real b
  obtain ⟨hd, hdb, hmax⟩ := rndUnbounded_satisfies F .toNegative ((b.val : Dyadic) : ℝ)
    (not_isUndefined_toNegative F)
  refine ⟨_, hd, by simpa using hmax 0 F.unbounded.zero_mem (by simpa using hb), hdb,
    fun v hv hbv => ?_⟩
  have h := abs_coe_real_le_of_boundOK (hFb ▸ hbv)
  rcases le_or_gt 0 (v : ℝ) with hv0 | hv0
  · rw [abs_of_nonneg hv0] at h ⊢
    exact hmax v hv h
  · rw [abs_of_neg hv0] at h ⊢
    have h' := hmax (-v) (FiniteFormat.neg_mem hv) (by rw [Dyadic.coe_real_neg]; exact h)
    rwa [Dyadic.coe_real_neg] at h'
private theorem localDoubleRounding_RTO_RN {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial) {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb)) :
    ∃ L, LocalDoubleRounding F₁ F₂ (.nearest tb) .toOdd L := by
  have hp_F₂ : ((2 : ℕ) : Prec) ≤ F₂.p := two_le_p_of_nontrivial_extend_two hsub hnt
  rcases hF₁b : F₁.b with _ | b₁
  · -- No bound on `F₁`, hence none on `F₂`: the finite rule applies everywhere.
    rw [Format.boundAfterNext_top (F := (F₁.extend 1).toFormat) hF₁b] at hsub
    have hF₂b := bound_top_of_withBound_top_subset hsub
    refine ⟨fun _ => True, fun _ => trivial, fun _ _ => trivial,
      fun _ _ => by rw [hF₂b]; trivial, fun _ hz hw hy => eq_of_rule (B := ⊤) h₁u ?_ hz hw hy
        trivial trivial⟩
    intro x z w hz hw
    refine roundsRTO_RN_finite (F₁ := F₁.withBoundFF ⊤) ?_ hz hw
    rw [Format.boundAfterNext_top (F := ((F₁.withBoundFF ⊤).extend 1).toFormat) rfl]
    exact hsub.trans F₂.subset_unbounded
  obtain ⟨d, hd, hd0, hdb, hdmax⟩ := exists_floor hF₁b
  -- Nontriviality makes the floor positive.
  have hd_pos : 0 < (d : ℝ) := by
    obtain ⟨v, hv, hv0⟩ := hnt
    exact (abs_pos.mpr fun h => hv0 (eq_zero_of_coe_real_zero h)).trans_le
      (hdmax v (mem_unbounded_of_mem hv) hv.2.2)
  have hdB : Format.boundOK (F₁.extend 1).toFormat.boundAfterNext d :=
    boundOK_boundAfterNext_of_boundOK (F₁ := F₁.extend 1)
      (by rw [show (F₁.extend 1).b = F₁.b from rfl, hF₁b]
          exact boundOK_coe_of_abs_le (by rwa [abs_of_nonneg hd0]))
  -- The midpoint `M` lies in `F₂`, and so is an `F₂`-bound.
  set M := ((F₁.extend 1).toFormat.next d : Dyadic)
  have hd1 : d ∈ (F₁.extend 1).unbounded := by
    have h := Format.self_subset_extend F₁.toFormat.unbounded 1 d hd
    exact ⟨h.1, h.2.1, trivial⟩
  have hM1 : M ∈ (F₁.extend 1).unbounded := next_mem_unbounded' hd1 hd0
  have hM_nn : 0 ≤ (M : ℝ) := hd0.trans (Format.lt_next d hd0).le
  have hMB : Format.boundOK (F₁.extend 1).toFormat.boundAfterNext M := by
    have hb₁ := nonneg_coe_real b₁
    have hnext := Format.next_nonneg (F₁.extend 1).toFormat b₁.val hb₁
    refine boundOK_of_abs_le ?_ (boundOK_boundAfterNext_next (F₁ := F₁.extend 1) hF₁b hnext)
    rw [abs_of_nonneg hM_nn, abs_of_nonneg hnext]
    exact next_mono (F := F₁.extend 1) hd0 hdb fun _ => hd_pos
  have hM_F₂ : M ∈ F₂ := by
    have h := Format.extend_mono F₁.toFormat.unbounded
      (by exact_mod_cast (by omega : (1 : ℕ) ≤ 2) : (1 : ℕ) ≤ 2) M hM1
    exact hsub _ ⟨h.1, h.2.1, hMB⟩
  have hM_u : M ∈ F₂.unbounded := mem_unbounded_of_mem hM_F₂
  have hguard : F₁.exp = ⊥ → 0 < (d : ℝ) := fun _ => hd_pos
  -- An in-bound nearest rounding puts its input within `M`.
  have pin : ∀ {x : ℝ} {y : Dyadic}, RoundsFinite F₁.unbounded (.nearest tb) x y →
      Format.boundOK F₁.b y → |x| ≤ M := fun hy hb =>
    abs_le_mid_of_nearest hd hd0 hguard hy (hdmax _ hy.1 hb)
  -- An inexact RTO result within `M` is strictly inside, and so is its input.
  have strict : ∀ {x : ℝ} {z : Dyadic}, RoundsFinite F₂.unbounded .toOdd x z →
      x ≠ (z : ℝ) → |(z : ℝ)| ≤ M → |(z : ℝ)| < M ∧ |x| < M := fun {x z} hz hxz hzM => by
    have hzM' : |(z : ℝ)| < M := lt_of_le_of_ne hzM (by
      rw [← abs_of_nonneg hM_nn]; exact abs_ne_of_toOdd hsub hp_F₂ hz hxz hM1 hMB)
    exact ⟨hzM', lt_of_not_ge fun h =>
      absurd (le_abs_faithful_of_le hM_u hM_nn h hz.2.1) (not_le.mpr hzM')⟩
  have hbound : ∀ {x : ℝ} {z : Dyadic}, |x| ≤ M → RoundsFinite F₂.unbounded .toOdd x z →
      Format.boundOK F₂.b z := fun hxM hz => by
    refine boundOK_of_abs_le ?_ hM_F₂.2.2
    rw [abs_of_nonneg hM_nn]
    exact abs_faithful_le_of_le hM_u hxM hz.2.1
  have hd0q : (0 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd0
  refine ⟨fun x => |x| ≤ M, fun ⟨hy, hb⟩ => pin hy hb, fun {x z w} ⟨hz, _⟩ ⟨hw, hbw⟩ => ?_,
    hbound, fun {x z w y} hxM hz hw hy => ?_⟩
  · rcases eq_or_ne x (z : ℝ) with hxz | hxz
    · rw [hxz]; exact pin hw hbw
    · exact (strict hz hxz (pin hw hbw)).2.le
  · rcases eq_or_ne x (z : ℝ) with hxz | hxz
    · exact RoundsFinite.unique h₁u (by rw [hxz]; exact hw) hy
    obtain ⟨hzM, hxM'⟩ := strict hz hxz (abs_faithful_le_of_le hM_u hxM hz.2.1)
    exact eq_of_rule (B := ((⟨d, hd0q⟩ : NonNegDyadic) : Bound)) h₁u
      (roundsRTO_RN_finite_of_extend (F₁ := F₁.withBoundFF (⟨d, hd0q⟩ : NonNegDyadic))
        (((withBound_subset_of_boundOK (F₁.extend 2).toFormat hdB).trans hsub).trans
          F₂.subset_unbounded) hp_F₂) hz hw hy
      (boundOK_coe_of_abs_le (abs_le_of_nearest_of_abs_lt_mid hd hd0 hguard hw hzM))
      (boundOK_coe_of_abs_le (abs_le_of_nearest_of_abs_lt_mid hd hd0 hguard hy hxM'))
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat}
    (hsub : ((F₁.extend 2).toFormat.withBound (F₁.extend 1).toFormat.boundAfterNext)
      ⊆ F₂.toFormat)
    (hnt : F₁.toFormat.Nontrivial)
    {tb : TieBreak} (h₁u : ¬ F₁.IsUndefined (.nearest tb)) (x : ℝ) :
    Overflows F₁ (.nearest tb) x ∨
    (∃ z w : Dyadic, RoundsInBound F₂ .toOdd x z ∧
      RoundsInBound F₁ (.nearest tb) (z : ℝ) w ∧
      RoundsInBound F₁ (.nearest tb) x w) :=
  (localDoubleRounding_RTO_RN hsub hnt h₁u).choose_spec.inBound h₁u
    (not_isUndefined_of_two_le_p (two_le_p_of_nontrivial_extend_two hsub hnt)) x
end Mpfx
