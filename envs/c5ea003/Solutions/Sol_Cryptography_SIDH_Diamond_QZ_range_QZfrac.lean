-- Prove2me | solution 1 for Cryptography.SIDH.Diamond.QZ_range_QZfrac
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T15:14:35.566239+00:00
-- url     : https://prove2.me/submissions/debc435f-d193-43f7-97a7-69ee1776bd44

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_KaniLemma

open Cryptography.SIDH Diamond in
theorem solution {n : ℕ} (hn : 0 < n) :
    (QZfrac n).range = nTorsion QZ n := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hval : ∀ k : ℤ, QZfrac n k = ((k * (n : ℚ)⁻¹ : ℚ) : QZ) := by
    intro k
    simp only [QZfrac, AddMonoidHom.comp_apply, zmultiplesHom_apply, QuotientAddGroup.mk'_apply,
      zsmul_eq_mul]
  ext x
  rw [AddMonoidHom.mem_range]
  constructor
  · -- `n • [k/n] = [k] = 0`
    rintro ⟨k, rfl⟩
    show (n : ℤ) • QZfrac n k = 0
    rw [hval, ← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
    refine AddSubgroup.mem_zmultiples_iff.2 ⟨k, ?_⟩
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one]
    push_cast
    field_simp
  · -- an `n`-torsion class `[q]` has `n q = m ∈ ℤ`, so `[q] = [m/n]`
    intro hx
    induction x using QuotientAddGroup.induction_on with
    | H q =>
      have hx' : (n : ℤ) • ((q : ℚ) : QZ) = 0 := hx
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff] at hx'
      obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.1 hx'
      rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hm
      refine ⟨m, ?_⟩
      rw [hval]
      congr 1
      rw [hm]
      push_cast
      field_simp
