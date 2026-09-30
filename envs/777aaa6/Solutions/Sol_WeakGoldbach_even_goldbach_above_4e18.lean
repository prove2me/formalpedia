-- Prove2me | solution 1 for WeakGoldbach.even_goldbach_above_4e18
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T22:48:55.223558+00:00
-- url     : https://prove2.me/submissions/8943d4cf-8bb1-4cfb-86f2-7805b155f0ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_symmetric_prime_pair_above_2e18

theorem solution (n : ℕ) (h : 4 * 10 ^ 18 < n) (he : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  obtain ⟨k, hk⟩ := he
  obtain ⟨t, htle, hpl, hpr⟩ :=
    WeakGoldbach.symmetric_prime_pair_above_2e18 k (by omega)
  exact ⟨k - t, k + t, hpl, hpr, by omega⟩
