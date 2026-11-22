-- Prove2me | solution 1 for P2M_Mpfx_rnd_lt_mid__f8e65c434f46
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:36:17.239693+00:00
-- url     : https://prove2.me/submissions/1601c1dc-f548-47fd-a8b8-d354e3c88432

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Theorems.Thm_Mpfx_rnd_lt_mid
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_RoundsFinite_isFaithfulRound
import Theorems.Thm_Mpfx_canonicalExp_eq_of_log_eq
import Theorems.Thm_Mpfx_log_eq_of_zpow_bounds
import Theorems.Thm_Mpfx_nearest_error_le_half_ulp
import Theorems.Thm_Mpfx_ofIntZpow_mem_unbounded
import Theorems.Thm_Mpfx_rndDown_add_ulp_le
import Theorems.Thm_Mpfx_ulp_of_ne_zero
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow


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
private theorem canonicalExp_eq_of_lt_mid {F₁ F₂ : FiniteFormat} {tb₂ : TieBreak} {x : ℝ}
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hmid : x < midp F₁ x - ulp F₂ x / 2)
    {z : Dyadic}
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z) :
    F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x := by
  set k := Int.log 2 x with hk
  set e₁ := F₁.canonicalExp x with he₁
  have h2e₁ : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
  have h_xhi : x < (2 : ℝ) ^ (k + 1) := by
    have := Int.lt_zpow_succ_log_self (b := 2) (by norm_num) x
    rw [← hk] at this; exact_mod_cast this
  -- upper bound `z < 2^(k+1)`: `z < midp F₁ x < 2^(k+1)`
  have hz_err := abs_le.mp (nearest_error_le_half_ulp hz)
  have hz_lt_midp : (z : ℝ) < midp F₁ x := by linarith [hz_err.2, hmid]
  have hmidp_lt : midp F₁ x < (2 : ℝ) ^ (k + 1) := by
    have h := rndDown_add_ulp_le F₁ hx hle
    rw [midp]; rw [ulp_of_ne_zero F₁ hx.ne'] at h ⊢; linarith
  exact canonicalExp_eq_of_binade_top hx h21 hle (hk ▸ lt_trans hz_lt_midp hmidp_lt) hz
end Mpfx
end

set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : _root_.Mpfx.Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : 0 < x)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hle : F₁.canonicalExp x ≤ Int.log 2 x + 1)
    (hmid : x < midp F₁ x - ulp F₂ x / 2)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w :=
  rnd_lt_mid hundef₁ hx.ne' h21 hmid (canonicalExp_eq_of_lt_mid hx h21 hle hmid hz) hz hw
end Mpfx
