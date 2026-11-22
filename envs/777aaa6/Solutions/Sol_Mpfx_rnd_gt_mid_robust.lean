-- Prove2me | solution 1 for Mpfx.rnd_gt_mid_robust
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:47:23.628723+00:00
-- url     : https://prove2.me/submissions/965fc98b-02c2-4685-a21d-67396a53ad17

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Theorems.Thm_Mpfx_rnd_gt_mid
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_inj
import Theorems.Thm_Mpfx_Dyadic_quantumAtLeast_coe_real
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_IsFaithfulRound_eq_of_mem
import Theorems.Thm_Mpfx_RoundsFinite_eq_of_mem
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_canonicalExp_eq_of_log_eq
import Theorems.Thm_Mpfx_log_eq_of_zpow_bounds
import Theorems.Thm_Mpfx_nearest_error_le_half_ulp
import Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded
import Theorems.Thm_Mpfx_ulp_le_half_ulp_of_canonicalExp_lt
import Theorems.Thm_Mpfx_ulp_of_ne_zero
import Theorems.Thm_Mpfx_ulp_pos
import Theorems.Thm_P2M_Mpfx_nearest_eq_of_close__390f66b23c83
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_inj


section
namespace Mpfx
private theorem canonicalExp_eq_of_binade_top {F₁ F₂ : FiniteFormat} {tb₂ : TieBreak} {x : ℝ}
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    {z : Dyadic}
    (hzhi : (z : ℝ) < (2 : ℝ) ^ (Int.log 2 x + 1))
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z) :
    F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x := by
  set k := Int.log 2 x with hk
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hxabs : |x| = x := abs_of_pos hx
  have h_xlo : (2 : ℝ) ^ k ≤ x := by
    have := Int.zpow_log_le_self (b := 2) (by norm_num) hx; rw [← hk] at this; exact_mod_cast this
  have he₂_le_k : F₂.canonicalExp x ≤ k := by omega
  have hzf : IsFaithfulRound F₂.unbounded x z := hz.isFaithfulRound
  have hdk_mem : Dyadic.ofIntZpow 1 k ∈ F₂.unbounded := by
    refine ofIntZpow_mem_unbounded F₂
      (fun he' => le_trans (F₂.exp_le_canonicalExp x he') he₂_le_k) (fun {p} _ => ?_)
    rw [abs_one]; exact one_le_pow₀ (by norm_num)
  have hdk_real : (Dyadic.ofIntZpow 1 k : ℝ) = (2 : ℝ) ^ k := by
    rw [Dyadic.coe_ofIntZpow]; push_cast; ring
  have h_zlo : (2 : ℝ) ^ k ≤ (z : ℝ) := by
    rcases hzf with ⟨_, _, hmax⟩ | ⟨_, hxz, _⟩
    · have := hmax _ hdk_mem (by rw [hdk_real]; exact h_xlo); rw [hdk_real] at this; exact this
    · linarith [h_xlo]
  have hz_pos : (0 : ℝ) < (z : ℝ) := lt_of_lt_of_le (zpow_pos (by norm_num) k) h_zlo
  have hlogz : Int.log 2 (z : ℝ) = k := log_eq_of_zpow_bounds hz_pos h_zlo hzhi
  have hzabs : |(z : ℝ)| = (z : ℝ) := abs_of_pos hz_pos
  exact (canonicalExp_eq_of_log_eq F₁ (ne_of_gt hz_pos) hx0
    (by rw [hzabs, hxabs, hlogz, ← hk])).trans rfl
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hmid : (rndUp F₁ x : ℝ) - ulp F₁ x / 2 + ulp F₂ x / 2 < x)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by
  set k := Int.log 2 x with hk
  have hx_hi : x < (2 : ℝ) ^ (k + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
    rw [← hk] at this; exact_mod_cast this
  by_cases hzc : (z : ℝ) < (2 : ℝ) ^ (k + 1)
  · -- no crossing: binade consistency, then `rnd_gt_mid`
    have hcexp : F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x :=
      canonicalExp_eq_of_binade_top hx h21 hle (by rw [← hk]; exact hzc) hz
    exact rnd_gt_mid hundef₁ hx.ne' h21 hmid hcexp hz hw
  · -- crossing: `z = 2^(k+1)`
    rw [not_lt] at hzc
    have hu2_le : ulp F₂ x ≤ ulp F₁ x / 2 := ulp_le_half_ulp_of_canonicalExp_lt hx.ne' h21
    have hu1pos := ulp_pos F₁ hx.ne'
    have hz_err := abs_le.mp (nearest_error_le_half_ulp hz)
    have hBmem₂ : Dyadic.ofIntZpow 1 (k + 1) ∈ F₂.unbounded := by
      refine ofIntZpow_mem_unbounded F₂
        (fun he' => le_trans (F₂.exp_le_canonicalExp x he') (by omega)) (fun {p} _ => ?_)
      rw [abs_one]; exact one_le_pow₀ (by norm_num)
    have hB_real : (Dyadic.ofIntZpow 1 (k + 1) : ℝ) = (2 : ℝ) ^ (k + 1) := by
      rw [Dyadic.coe_ofIntZpow]; push_cast; ring
    have hzf : IsFaithfulRound F₂.unbounded x z := hz.isFaithfulRound
    have hz_eq : (z : ℝ) = (2 : ℝ) ^ (k + 1) := by
      rcases hzf with ⟨_, hzx, _⟩ | ⟨_, _, hmin⟩
      · exfalso; linarith [hzx, hx_hi, hzc]
      · have := hmin _ hBmem₂ (by rw [hB_real]; exact le_of_lt hx_hi)
        rw [hB_real] at this; linarith [this, hzc]
    have hzmem₁ : z ∈ F₁.unbounded := by
      have hzB : z = Dyadic.ofIntZpow 1 (k + 1) :=
        (Dyadic.coe_real_inj _ _).mp (by rw [hz_eq, hB_real])
      rw [hzB]
      refine ofIntZpow_mem_unbounded F₁
        (fun he' => le_trans (F₁.exp_le_canonicalExp x he') (by omega)) (fun {p} _ => ?_)
      rw [abs_one]; exact one_le_pow₀ (by norm_num)
    have hw_eq : w = z := RoundsFinite.eq_of_mem hzmem₁ hw
    have hx_close : |x - (z : ℝ)| < (2 : ℝ) ^ (F₁.canonicalExp x) / 2 := by
      have h1 : (2 : ℝ) ^ (k + 1) - x ≤ ulp F₂ x / 2 := by
        have := hz_err.2; rw [hz_eq] at this; linarith
      have hu1 : ulp F₁ x = (2 : ℝ) ^ (F₁.canonicalExp x) := ulp_of_ne_zero F₁ hx.ne'
      rw [hz_eq, abs_of_nonpos (by linarith [hx_hi] : x - (2 : ℝ) ^ (k + 1) ≤ 0), ← hu1]
      linarith [h1, hu2_le, hu1pos]
    have hquant_z : Dyadic.quantumAtLeast ((F₁.canonicalExp x : ℤ) : QExp) z := by
      refine (Dyadic.quantumAtLeast_coe_real (F₁.canonicalExp x) z).mpr
        ⟨2 ^ (k + 1 - F₁.canonicalExp x).toNat, ?_⟩
      rw [hz_eq]; push_cast
      rw [← zpow_natCast (2 : ℝ), Int.toNat_of_nonneg (by omega),
          ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1; ring
    rw [hw_eq]
    exact nearest_eq_of_close' F₁ tb₁ x hundef₁ hquant_z hx_close
end Mpfx
