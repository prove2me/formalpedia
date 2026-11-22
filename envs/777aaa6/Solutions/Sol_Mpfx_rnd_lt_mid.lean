-- Prove2me | solution 1 for Mpfx.rnd_lt_mid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:34:34.737149+00:00
-- url     : https://prove2.me/submissions/a2be14db-e030-4e02-9b0e-91309ae68ec6

import Definitions.Def_Mpfx_Rounding_Ulp
import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_Containment
import Definitions.Def_Mpfx_DoubleRounding_NearestMidpoint
import Theorems.Thm_Mpfx_Dyadic_coe_ofIntZpow
import Theorems.Thm_Mpfx_Dyadic_coe_real_zero
import Theorems.Thm_Mpfx_Dyadic_ext_real
import Theorems.Thm_Mpfx_FiniteFormat_unbounded_isUndefined
import Theorems.Thm_Mpfx_RoundsFinite_eq_zero_of_zero
import Theorems.Thm_Mpfx_RoundsFinite_unique
import Theorems.Thm_Mpfx_mul_zpow_neg_self
import Theorems.Thm_Mpfx_nearest_eq_rndDown_of_lt_midp
import Theorems.Thm_Mpfx_nearest_eq_rndUp_of_midp_lt
import Theorems.Thm_Mpfx_nearest_error_le_half_ulp
import Theorems.Thm_Mpfx_rndDown_eq
import Theorems.Thm_Mpfx_rndDown_le
import Theorems.Thm_Mpfx_rndUnbounded_satisfies
import Theorems.Thm_Mpfx_rndUp_eq
import Theorems.Thm_Mpfx_ulp_eq_zpow_of
import Theorems.Thm_Mpfx_ulp_le_half_ulp_of_canonicalExp_lt
import Theorems.Thm_Mpfx_ulp_of_ne_zero
import Theorems.Thm_Mpfx_ulp_pos
attribute [local simp] Mpfx.Dyadic.coe_ofIntZpow
attribute [local simp] Mpfx.Dyadic.coe_real_zero
attribute [local simp] Mpfx.FiniteFormat.unbounded_isUndefined



set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution {F₁ F₂ : FiniteFormat} {tb₁ tb₂ : TieBreak} {x : ℝ}
    {z w : Dyadic}
    (hundef₁ : ¬ F₁.IsUndefined (.nearest tb₁))
    (hx : x ≠ 0)
    (h21 : F₂.canonicalExp x < F₁.canonicalExp x)
    (hmid : x < midp F₁ x - ulp F₂ x / 2)
    (hcexp : F₁.canonicalExp (z : ℝ) = F₁.canonicalExp x)
    (hz : RoundsFinite F₂.unbounded (.nearest tb₂) x z)
    (hw : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) w) :
    RoundsFinite F₁.unbounded (.nearest tb₁) x w := by
  set e₁ := F₁.canonicalExp x with he₁
  set m : ℤ := ⌊x * (2 : ℝ) ^ (-e₁)⌋ with hm
  have h2e₁ : (0 : ℝ) < (2 : ℝ) ^ e₁ := zpow_pos (by norm_num) _
  have hA : (rndDown F₁ x : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ := by
    rw [rndDown_eq, Dyadic.coe_ofIntZpow, ← he₁, ← hm]
  have hmidx : midp F₁ x = (m : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
    rw [midp, ulp_of_ne_zero F₁ hx, hA, ← he₁]
  -- real bounds on x and z
  have hax : (m : ℝ) * (2 : ℝ) ^ e₁ ≤ x := hA ▸ rndDown_le F₁ x
  have hulp₂_pos : (0 : ℝ) < ulp F₂ x := ulp_pos F₂ hx
  have hx_lt_midp : x < midp F₁ x := by linarith [hmid]
  have hz_err := abs_le.mp (nearest_error_le_half_ulp hz)
  have hulp_gap : ulp F₂ x ≤ ulp F₁ x / 2 := ulp_le_half_ulp_of_canonicalExp_lt hx h21
  have hulp₁_eq : ulp F₁ x = (2 : ℝ) ^ e₁ := by rw [ulp_of_ne_zero F₁ hx, ← he₁]
  have hz_lt : (z : ℝ) < (m : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
    rw [hmidx] at hmid; linarith [hz_err.2]
  have hz_gt : (m : ℝ) * (2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₁ / 2 < (z : ℝ) := by
    rw [hulp₁_eq] at hulp_gap; linarith [hz_err.1, hax, hulp_gap, hulp₂_pos]
  -- scaled mantissa of z
  set s := (z : ℝ) * (2 : ℝ) ^ (-e₁) with hs
  have hzs : (z : ℝ) = s * (2 : ℝ) ^ e₁ := by rw [hs, mul_zpow_neg_self]
  -- `a := rndDown F₁ x` is the F₁-nearest rounding of z (two cell sub-cases)
  have hP2 : RoundsFinite F₁.unbounded (.nearest tb₁) (z : ℝ) (rndDown F₁ x) := by
    rcases lt_or_ge (z : ℝ) ((m : ℝ) * (2 : ℝ) ^ e₁) with hza | hza
    · -- z < a: ⌈s⌉ = m, so rndUp F₁ z = rndDown F₁ x and midp F₁ z < z
      have hfloor : ⌊s⌋ = m - 1 := by
        rw [Int.floor_eq_iff]
        refine ⟨?_, ?_⟩
        · push_cast; nlinarith [hz_gt, hzs, h2e₁]
        · push_cast; nlinarith [hza, hzs, h2e₁]
      have hceil : ⌈s⌉ = m := by
        have h1 : ⌈s⌉ ≤ ⌊s⌋ + 1 := Int.ceil_le_floor_add_one _
        have hlt : (m - 1 : ℝ) < s := by nlinarith [hz_gt, hzs, h2e₁]
        have h3 : (m : ℤ) ≤ ⌈s⌉ := by
          have hcr : ((m - 1 : ℤ) : ℝ) < (⌈s⌉ : ℝ) :=
            lt_of_lt_of_le (by push_cast; linarith) (Int.le_ceil s)
          have : (m - 1 : ℤ) < ⌈s⌉ := by exact_mod_cast hcr
          omega
        omega
      have hru_eq : rndUp F₁ (z : ℝ) = rndDown F₁ x := by
        rw [rndUp_eq, rndDown_eq, hcexp, ← he₁, ← hs, hceil, ← hm]
      have hmidz : midp F₁ (z : ℝ) < (z : ℝ) := by
        have hmz : midp F₁ (z : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ - (2 : ℝ) ^ e₁ / 2 := by
          have hrd_eq : rndDown F₁ (z : ℝ) = Dyadic.ofIntZpow (m - 1) e₁ := by
            rw [rndDown_eq, hcexp, ← hs, hfloor]
          -- `z = 0` would force `m = 1`, contradicting `hz_gt`.
          have hg : ¬((z : ℝ) = 0 ∧ F₁.exp = ⊥) := by
            rintro ⟨hz0, -⟩
            have hs0 : s = 0 := by rw [hs, hz0, zero_mul]
            have hm1 : m = 1 := by rw [hs0, Int.floor_zero] at hfloor; omega
            rw [hm1] at hz_gt; rw [hz0] at hz_gt; push_cast at hz_gt; linarith
          rw [midp, ulp_eq_zpow_of F₁ hg, hrd_eq, Dyadic.coe_ofIntZpow, hcexp]
          push_cast; ring
        rw [hmz]; exact hz_gt
      have := nearest_eq_rndUp_of_midp_lt F₁ tb₁ (z : ℝ) hundef₁ hmidz
      rwa [hru_eq] at this
    · -- z ≥ a: ⌊s⌋ = m, so rndDown F₁ z = rndDown F₁ x and z < midp F₁ z
      have hfloor : ⌊s⌋ = m := by
        rw [Int.floor_eq_iff]
        refine ⟨?_, ?_⟩
        · nlinarith [hza, hzs, h2e₁]
        · nlinarith [hz_lt, hzs, h2e₁]
      have hrd_eq : rndDown F₁ (z : ℝ) = rndDown F₁ x := by
        rw [rndDown_eq, rndDown_eq, hcexp, ← he₁, ← hs, hfloor, ← hm]
      by_cases hg : (z : ℝ) = 0 ∧ F₁.exp = ⊥
      · -- no minimum quantum and `z = 0`: both roundings are `0`
        obtain ⟨hz0, -⟩ := hg
        have hs0 : s = 0 := by rw [hs, hz0, zero_mul]
        have hm0 : m = 0 := by rw [hs0, Int.floor_zero] at hfloor; omega
        have hA0 : rndDown F₁ x = 0 := by
          have : ((rndDown F₁ x : Dyadic) : ℝ) = 0 := by rw [hA, hm0]; push_cast; ring
          exact Dyadic.ext_real (by rw [this, Dyadic.coe_real_zero])
        rw [hA0, hz0]
        have hu : ¬ (F₁.unbounded).IsUndefined (.nearest tb₁) := hundef₁
        have hsat := rndUnbounded_satisfies F₁.unbounded (.nearest tb₁) 0 hu
        rwa [RoundsFinite.eq_zero_of_zero hsat] at hsat
      · have hmidz : (z : ℝ) < midp F₁ (z : ℝ) := by
          have hmz : midp F₁ (z : ℝ) = (m : ℝ) * (2 : ℝ) ^ e₁ + (2 : ℝ) ^ e₁ / 2 := by
            rw [midp, ulp_eq_zpow_of F₁ hg, hrd_eq, hA, hcexp]
          rw [hmz]; exact hz_lt
        have := nearest_eq_rndDown_of_lt_midp F₁ tb₁ (z : ℝ) hundef₁ hmidz
        rwa [hrd_eq] at this
  -- w = rndDown F₁ x by nearest-uniqueness, then round `x` below its midpoint
  have hu₁ : ¬ (F₁.unbounded).IsUndefined (.nearest tb₁) := by
    rw [FiniteFormat.unbounded_isUndefined]; exact hundef₁
  have hw_eq : w = rndDown F₁ x := RoundsFinite.unique hu₁ hw hP2
  rw [hw_eq]
  exact nearest_eq_rndDown_of_lt_midp F₁ tb₁ x hundef₁ hx_lt_midp
end Mpfx
