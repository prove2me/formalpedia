-- Prove2me | Theorems.Thm_flt5_pow5_sum_natAbs_bound
-- name    : flt5_pow5_sum_natAbs_bound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T15:48:56.623572+00:00
-- url     : https://prove2.me/theorems/cc90e7b9-e674-4166-b139-a4dbfe5eb7dd

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem flt5_pow5_sum_natAbs_bound (p q c1 : ℤ) (h : p ^ 5 + q ^ 5 = c1 ^ 5) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : 0 < p * q) : p.natAbs ≤ c1.natAbs ∧ q.natAbs ≤ c1.natAbs := by sorry
