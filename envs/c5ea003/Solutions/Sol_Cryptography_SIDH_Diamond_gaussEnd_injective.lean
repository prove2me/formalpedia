-- Prove2me | solution 1 for Cryptography.SIDH.Diamond.gaussEnd_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:18:35.701263+00:00
-- url     : https://prove2.me/submissions/e261f487-485e-4e7c-ae43-ddcb02681c5f

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_KaniLemma

open Cryptography.SIDH Diamond in
theorem solution : Function.Injective gaussEnd := by
  -- an integer killing all of `ℚ/ℤ` is zero
  have key : ∀ u : ℤ, (∀ t : QZ, u • t = 0) → u = 0 := by
    intro u hu
    have h := hu (((1 : ℚ) / ((|u| : ℤ) + 1 : ℤ) : ℚ) : QZ)
    rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff] at h
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 h
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hm
    have hpos : (0 : ℤ) < |u| + 1 := by positivity
    have hposq : (0 : ℚ) < ((|u| + 1 : ℤ) : ℚ) := by exact_mod_cast hpos
    have hq : (m : ℚ) * ((|u| + 1 : ℤ) : ℚ) = u := by
      rw [hm]
      field_simp
    have hz : m * (|u| + 1) = u := by exact_mod_cast hq
    have habs : |m| * (|u| + 1) = |u| := by
      rw [← abs_of_pos hpos, ← abs_mul, hz]
    by_contra hu0
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hz
      exact hu0 hz.symm
    have h1 : 1 ≤ |m| := Int.one_le_abs hm0
    nlinarith [abs_nonneg u]
  rw [injective_iff_map_eq_zero]
  intro z hz
  have happ : ∀ t : QZ, gaussHom z.re z.im (t, 0) = 0 := fun t => DFunLike.congr_fun hz (t, 0)
  have hre : z.re = 0 := key _ fun t => by
    have := congrArg Prod.fst (happ t)
    simpa using this
  have him : z.im = 0 := key _ fun t => by
    have := congrArg Prod.snd (happ t)
    simpa using this
  exact Zsqrtd.ext (by simpa using hre) (by simpa using him)
