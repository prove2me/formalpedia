-- Prove2me | solution 1 for mme_entropy_surplus_arith
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T08:08:16.426065+00:00
-- url     : https://prove2.me/submissions/81b4a115-1eb9-4ee0-81e7-540e39746df6

import Definitions.Def_mme_entropy_regional_CW_recipe
open MME MME.ProfiledCW MME.RegionRealization
set_option autoImplicit false

theorem solution : ((49 : ℕ) : ℝ) < ((5 : ℕ) : ℝ) * (((25 : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000)) := by
  have htau : (3 : ℝ) / 4 ≤ (3952233 : ℝ) / 5000000 := by norm_num
  have hbase : (1 : ℝ) ≤ ((25 : ℕ) : ℝ) := by norm_num
  have hmono : (((25 : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ≤ (((25 : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000)) :=
    Real.rpow_le_rpow_of_exponent_le hbase htau
  have hx_nonneg : (0 : ℝ) ≤ ((25 : ℕ) : ℝ) := by positivity
  have hpow : ((((25 : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ)) = (15625 : ℝ) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul hx_nonneg]
    have hexp : ((3 : ℝ) / 4) * ((((4 : ℕ)) : ℝ)) = ((((3 : ℕ)) : ℝ)) := by norm_num
    rw [hexp, Real.rpow_natCast]
    norm_num
  have hlt4 : (((49 : ℝ) / 5) ^ (4 : ℕ)) < ((((25 : ℕ) : ℝ) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ)) := by
    rw [hpow]
    norm_num
  have hb_nonneg : (0 : ℝ) ≤ ((((25 : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) :=
    Real.rpow_nonneg hx_nonneg _
  have hbase_lt : (49 : ℝ) / 5 < ((((25 : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) :=
    lt_of_pow_lt_pow_left₀ 4 hb_nonneg hlt4
  have h5pos : (0 : ℝ) < 5 := by norm_num
  have h49mid : (49 : ℝ) < 5 * ((((25 : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) :=
    (div_lt_iff₀' h5pos).mp hbase_lt
  have h5mono : 5 * ((((25 : ℕ) : ℝ) ^ ((3 : ℝ) / 4))) ≤ 5 * ((((25 : ℕ) : ℝ) ^ ((3952233 : ℝ) / 5000000))) :=
    mul_le_mul_of_nonneg_left hmono (by norm_num)
  have h49cast : ((((49 : ℕ))) : ℝ) = (49 : ℝ) := by norm_num
  have h5cast : ((((5 : ℕ))) : ℝ) = (5 : ℝ) := by norm_num
  rw [h49cast, h5cast]
  exact lt_of_lt_of_le h49mid h5mono
