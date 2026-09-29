-- Prove2me | solution 1 for mme_CW_2376_profile_weight_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T16:29:03.760632+00:00
-- url     : https://prove2.me/submissions/f7f2bb5c-b07e-43cf-bebb-3c0a98e0caec

import Mathlib.Tactic
import Definitions.Def_mme_CW_2376_profile_data

open MME

theorem solution
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (Vc : ℝ) (hVc_nonneg : 0 ≤ Vc)
    (m : ℕ)
    (delta : ℝ) (hdelta_pos : 0 < delta) (hdelta_lt : delta < 1)
    (W : ℝ) (hW_nonneg : 0 ≤ W)
    (hW : Vc ^ m * (1 - delta) ≤ W) :
    cw2376ProfileNumeratorBase tau Vc ^ (3000000 * m) *
        (1 - delta) ^ (616627 : ℕ) ≤
      ((((cw2376ProfileSide m * cw2376ProfileSide m *
          cw2376ProfileSide m : ℕ) : ℝ) ^ tau) *
        W ^ (616627 : ℕ)) := by
  have herr_nonneg : 0 ≤ 1 - delta := by linarith
  have hbase_nonneg : 0 ≤ Vc ^ m * (1 - delta) :=
    mul_nonneg (pow_nonneg hVc_nonneg m) herr_nonneg
  have hpow : (Vc ^ m * (1 - delta)) ^ (616627 : ℕ) ≤
      W ^ (616627 : ℕ) :=
    pow_le_pow_left₀ hbase_nonneg hW 616627
  have hside_nonneg : 0 ≤
      ((((cw2376ProfileSide m * cw2376ProfileSide m *
        cw2376ProfileSide m : ℕ) : ℝ) ^ tau)) :=
    Real.rpow_nonneg (by positivity) _
  have hmul := mul_le_mul_of_nonneg_left hpow hside_nonneg
  have h12 :
      (12 : ℝ) ^
          (6 * tau * cw2376_b * (((3000000 * m : ℕ) : ℝ))) =
        ((12 : ℝ) ^ (((75036 * m : ℕ) : ℝ) * tau)) ^ (3 : ℕ) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 12)]
    congr 1
    unfold cw2376_b
    norm_num
    ring
  have h38 :
      (38 : ℝ) ^
          (3 * tau * cw2376_c * (((3000000 * m : ℕ) : ℝ))) =
        ((38 : ℝ) ^ (((307638 * m : ℕ) : ℝ) * tau)) ^ (3 : ℕ) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 38)]
    congr 1
    unfold cw2376_c
    norm_num
    ring
  have hVc :
      Vc ^ (cw2376_d * (((3000000 * m : ℕ) : ℝ))) =
        (Vc ^ m) ^ (616627 : ℕ) := by
    rw [← Real.rpow_natCast Vc m,
      ← Real.rpow_mul_natCast hVc_nonneg]
    congr 1
    unfold cw2376_d
    norm_num
    ring
  have hside :
      ((((cw2376ProfileSide m * cw2376ProfileSide m *
          cw2376ProfileSide m : ℕ) : ℝ) ^ tau)) =
        ((12 : ℝ) ^ (((75036 * m : ℕ) : ℝ) * tau) *
          (38 : ℝ) ^ (((307638 * m : ℕ) : ℝ) * tau)) *
        ((12 : ℝ) ^ (((75036 * m : ℕ) : ℝ) * tau) *
          (38 : ℝ) ^ (((307638 * m : ℕ) : ℝ) * tau)) *
        ((12 : ℝ) ^ (((75036 * m : ℕ) : ℝ) * tau) *
          (38 : ℝ) ^ (((307638 * m : ℕ) : ℝ) * tau)) := by
    unfold cw2376ProfileSide
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity)]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 12),
      ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 38)]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hnumer :
      cw2376ProfileNumeratorBase tau Vc ^ (3000000 * m) =
        (((cw2376ProfileSide m * cw2376ProfileSide m *
            cw2376ProfileSide m : ℕ) : ℝ) ^ tau) *
          (Vc ^ m) ^ (616627 : ℕ) := by
    unfold cw2376ProfileNumeratorBase
    rw [mul_pow, mul_pow]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 12),
      ← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 38),
      ← Real.rpow_mul_natCast hVc_nonneg]
    rw [h12, h38, hVc, hside]
    ring
  have hidentity :
      cw2376ProfileNumeratorBase tau Vc ^ (3000000 * m) *
          (1 - delta) ^ (616627 : ℕ) =
        (((cw2376ProfileSide m * cw2376ProfileSide m *
            cw2376ProfileSide m : ℕ) : ℝ) ^ tau) *
          (Vc ^ m * (1 - delta)) ^ (616627 : ℕ) := by
    rw [hnumer, mul_pow]
    ac_rfl
  exact hidentity.trans_le hmul
