-- Prove2me | solution 1 for Mpfx.floor_minimality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T05:59:25.926517+00:00
-- url     : https://prove2.me/submissions/9fc2220c-2c5e-4655-bb6d-20e771316cfa

import Definitions.Def_Mpfx_Format_Discrete
import Definitions.Def_Mpfx_Format_CanonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_le_iff
import Theorems.Thm_Mpfx_FiniteFormat_canonicalExp_mono
import Theorems.Thm_Mpfx_FiniteFormat_exists_mul_zpow_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_exp_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_log_sub_p_le_canonicalExp
import Theorems.Thm_Mpfx_FiniteFormat_p_pos
import Theorems.Thm_Mpfx_exp_le_log_of_mem
import Theorems.Thm_Mpfx_two_zpow_shift
import Theorems.Thm_Mpfx_two_zpow_split_toNat


set_option autoImplicit true
open Mpfx
namespace Mpfx
theorem _root_.solution (F : FiniteFormat) (x : ℝ) {z : Dyadic}
    (hz_prec : Dyadic.precisionAtMost F.p z)
    (hz_quant : Dyadic.quantumAtLeast F.exp z) (hz_le_x : (z : ℝ) ≤ x) :
    (z : ℝ) ≤ (⌊x * (2 : ℝ) ^ (-(F.canonicalExp x))⌋ : ℝ) *
              (2 : ℝ) ^ (F.canonicalExp x) := by
  set e := F.canonicalExp x
  have h2e : (0 : ℝ) < (2 : ℝ) ^ e := zpow_pos two_pos e
  -- A multiple of `2^e` at most `x` is at most the floor projection.
  have hmul : ∀ k : ℤ, (k : ℝ) * (2 : ℝ) ^ e ≤ x →
      (k : ℝ) * (2 : ℝ) ^ e ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) * (2 : ℝ) ^ e := fun k hk => by
    have : (k : ℝ) ≤ x * (2 : ℝ) ^ (-e) := by
      rw [zpow_neg, ← div_eq_mul_inv, le_div_iff₀ h2e]; exact hk
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Int.le_floor.mpr this) h2e.le
  have hz : z ∈ F.unbounded := ⟨hz_prec, hz_quant, trivial⟩
  -- If `z`'s own step is at least `x`'s, `z` is a multiple of `2^e`.
  by_cases hce : e ≤ F.canonicalExp (z : ℝ)
  · obtain ⟨m, hm⟩ := F.exists_mul_zpow_canonicalExp hz
    rw [hm.trans (two_zpow_shift m hce)] at hz_le_x ⊢
    exact hmul _ hz_le_x
  push Not at hce
  rcases le_or_gt (z : ℝ) 0 with hz0 | hz0
  · rcases le_or_gt 0 x with hx0 | hx0
    · -- The floor projection of a nonnegative `x` is nonnegative.
      have : (0 : ℝ) ≤ (⌊x * (2 : ℝ) ^ (-e)⌋ : ℝ) := by
        exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hx0 (zpow_pos two_pos _).le)
      nlinarith
    · -- `z ≤ x < 0` makes `|x| ≤ |z|`, so `cexp x ≤ cexp z`.
      have habs : |x| ≤ |(z : ℝ)| := by
        rw [abs_of_neg hx0, abs_of_nonpos hz0]; linarith
      exact absurd (F.canonicalExp_mono hx0.ne habs) (not_le.mpr hce)
  -- `0 < z ≤ x` with a finer step: the precision term binds at `x`, so `z` lies
  -- below `2^⌊log₂ x⌋`, a multiple of `2^e` at most `x`.
  have hx0 : 0 < x := hz0.trans_le hz_le_x
  set L := Int.log 2 x
  obtain ⟨p, hp, hpz⟩ : ∃ p : ℕ, F.p = p ∧ F.canonicalExp (z : ℝ) < Int.log 2 |x| + 1 - p := by
    by_contra h
    push Not at h
    exact absurd ((F.canonicalExp_le_iff hx0.ne').mpr ⟨h, fun e' he' =>
      F.exp_le_canonicalExp _ he'⟩) (not_le.mpr hce)
  rw [abs_of_pos hx0] at hpz
  have hzL : (z : ℝ) < (2 : ℝ) ^ L := by
    have h1 := F.log_sub_p_le_canonicalExp hz0.ne' hp
    rw [abs_of_pos hz0] at h1
    calc (z : ℝ) < (2 : ℝ) ^ (Int.log 2 (z : ℝ) + 1) := Int.lt_zpow_succ_log_self (by norm_num) _
      _ ≤ (2 : ℝ) ^ L := zpow_le_zpow_right₀ (by norm_num) (by omega)
  have heL : e ≤ L := by
    refine (F.canonicalExp_le_iff hx0.ne').mpr ⟨fun q hq => ?_, fun e' he' => ?_⟩
    · have := F.p_pos hq; rw [abs_of_pos hx0]; omega
    · have h1 := exp_le_log_of_mem F he' hz hz0
      have h2 := Int.log_mono_right (b := 2) hz0 hz_le_x
      omega
  have hLx : (2 : ℝ) ^ L ≤ x := Int.zpow_log_le_self (by norm_num) hx0
  have hpow : (((2 : ℤ) ^ (L - e).toNat : ℤ) : ℝ) * (2 : ℝ) ^ e = (2 : ℝ) ^ L := by
    rw [two_zpow_split_toNat heL]; push_cast; ring
  have h := hmul _ (by rw [hpow]; exact hLx)
  rw [hpow] at h
  linarith
end Mpfx
