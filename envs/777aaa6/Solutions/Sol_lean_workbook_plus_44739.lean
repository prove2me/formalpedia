-- Prove2me | solution 1 for lean_workbook_plus_44739
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:13:04.453294+00:00
-- url     : https://prove2.me/submissions/0b2a04bf-ea35-4cdf-8670-1a56ea8b6292

import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

private lemma central_product_divisibility (m : ℕ) :
    2^m ∣ ∏ i ∈ Finset.range m, Nat.centralBinom (i+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Finset.prod_range_succ]
    exact mul_dvd_mul ih (Nat.two_dvd_centralBinom_succ m)

set_option maxRecDepth 4096 in
theorem solution (n : ℕ) (hn : n = 64) :
    2^n ∣ (Nat.choose 2 1 * Nat.choose 4 2 * Nat.choose 6 3 * Nat.choose 8 4 * Nat.choose 10 5 * Nat.choose 12 6 * Nat.choose 14 7 * Nat.choose 16 8 * Nat.choose 18 9 * Nat.choose 20 10 * Nat.choose 22 11 * Nat.choose 24 12 * Nat.choose 26 13 * Nat.choose 28 14 * Nat.choose 30 15 * Nat.choose 32 16 * Nat.choose 34 17 * Nat.choose 36 18 * Nat.choose 38 19 * Nat.choose 40 20 * Nat.choose 42 21 * Nat.choose 44 22 * Nat.choose 46 23 * Nat.choose 48 24 * Nat.choose 50 25 * Nat.choose 52 26 * Nat.choose 54 27 * Nat.choose 56 28 * Nat.choose 58 29 * Nat.choose 60 30 * Nat.choose 62 31 * Nat.choose 64 32 * Nat.choose 66 33 * Nat.choose 68 34 * Nat.choose 70 35 * Nat.choose 72 36 * Nat.choose 74 37 * Nat.choose 76 38 * Nat.choose 78 39 * Nat.choose 80 40 * Nat.choose 82 41 * Nat.choose 84 42 * Nat.choose 86 43 * Nat.choose 88 44 * Nat.choose 90 45 * Nat.choose 92 46 * Nat.choose 94 47 * Nat.choose 96 48 * Nat.choose 98 49 * Nat.choose 100 50 * Nat.choose 102 51 * Nat.choose 104 52 * Nat.choose 106 53 * Nat.choose 108 54 * Nat.choose 110 55 * Nat.choose 112 56 * Nat.choose 114 57 * Nat.choose 116 58 * Nat.choose 118 59 * Nat.choose 120 60 * Nat.choose 122 61 * Nat.choose 124 62 * Nat.choose 126 63 * Nat.choose 128 64) := by
  subst n
  simpa only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.centralBinom,
    Nat.reduceAdd, Nat.reduceMul, one_mul] using central_product_divisibility 64
