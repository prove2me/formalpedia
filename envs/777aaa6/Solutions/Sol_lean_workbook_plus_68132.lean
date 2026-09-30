-- Prove2me | solution 1 for lean_workbook_plus_68132
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:04:46.372582+00:00
-- url     : https://prove2.me/submissions/d7581467-119f-42c2-a10d-804d83368c5d

import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

private theorem lifted_congruence (k : ℕ) : 1994 ∣ 10 ^ (9 * k) - 2 ^ (10 * k) := by
  have hbase : Nat.ModEq 1994 (2 ^ 10) (10 ^ 9) := by decide
  have hle : (2 ^ 10) ^ k ≤ (10 ^ 9) ^ k :=
    Nat.pow_le_pow_left (by norm_num) k
  have hdiv := (Nat.modEq_iff_dvd' hle).mp (hbase.pow k)
  simpa only [← pow_mul] using hdiv

theorem solution : 1994 ∣ (10 ^ 900 - 2 ^ 1000) := by
  simpa only [Nat.reduceMul] using lifted_congruence 100
