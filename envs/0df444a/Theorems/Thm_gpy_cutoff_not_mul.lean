-- Prove2me | Theorems.Thm_gpy_cutoff_not_mul
-- name    : gpy_cutoff_not_mul
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:53:42.134012+00:00
-- url     : https://prove2.me/theorems/bd6cc2f8-1378-47b8-a638-c42f6c8ea59f
-- title:
--   Selberg cutoff does not factor over sums
-- statement:
--   Let deg be a natural number with deg >= 1. Then the polynomial cutoff does not factor over sums: (1 - (1/2 + 1/2))^deg is not equal to (1 - 1/2)^deg * (1 - 1/2)^deg. Indeed, at s1 = s2 = 1/2 the left side is (1 - 1)^deg = 0 while the right side is (1/2)^(2*deg) > 0. This is the structural reason the Selberg weight has no pure Euler product: log(D1*D2) adds, but the cutoff polynomial does not split over addition. SCOPE, stated honestly: this proves the polynomial identity fails; it does NOT by itself refute cutoff factorization on the integer lattice (exhibiting coprime integers D1, D2 with c(D1*D2) != c(D1)*c(D2) would need transcendence results about logarithms of integers, which are not claimed here).
-- source:
--   GPY Euler-product analysis: the polynomial cutoff does not factor over sums, proved by evaluation at s1 = s2 = 1/2

import Mathlib
open Classical

theorem gpy_cutoff_not_mul {deg : ℕ} (hdeg : 1 ≤ deg) :
    (1 - ((1 : ℝ) / 2 + (1 : ℝ) / 2)) ^ deg ≠
      (1 - (1 : ℝ) / 2) ^ deg * (1 - (1 : ℝ) / 2) ^ deg := by sorry
