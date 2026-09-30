-- Prove2me | solution 1 for lean_workbook_plus_69080
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:17:19.421122+00:00
-- url     : https://prove2.me/submissions/2b68bea5-ede0-41e6-8e01-c5cb221b84d8

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

private theorem block_family (k : ℕ) :
    2013 ∣ (10000 ^ (165 * k) - 1) / 9999 := by
  have hbase : Nat.ModEq (9999 * 2013) 1 (10000 ^ 165) := by
    norm_num [Nat.ModEq]
  have hle : 1 ^ k ≤ (10000 ^ 165) ^ k :=
    Nat.pow_le_pow_left (by norm_num) k
  have hdiv := (Nat.modEq_iff_dvd' hle).mp (hbase.pow k)
  apply Nat.dvd_div_of_mul_dvd
  simpa only [one_pow, ← pow_mul] using hdiv

theorem solution (hn : 0 < 165) :
    2013 ∣ (10 ^ (4 * 165) - 1) / (10 ^ 4 - 1) := by
  simpa only [Nat.mul_one, pow_mul, Nat.reducePow, Nat.reduceSub] using block_family 1
