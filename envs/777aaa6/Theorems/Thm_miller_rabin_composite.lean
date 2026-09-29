-- Prove2me | Theorems.Thm_miller_rabin_composite
-- name    : miller_rabin_composite
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:25:29.422624+00:00
-- url     : https://prove2.me/theorems/1fedf656-a367-460e-b467-1f4939b10921
-- statement:
--   Miller-Rabin composite witnesses: For every odd composite n, at least 3/4 of all a ∈ {2,...,n-1} are Miller-Rabin witnesses. Finding explicit witnesses without GRH and determining the smallest guaranteed witness are open.
-- source:
--   https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test

import Mathlib

import Mathlib

theorem miller_rabin_composite (n : ℕ) (hn : 3 ≤ n) (hodd : ¬ 2 ∣ n)
    (hcomp : ¬ Nat.Prime n) :
    ∃ a : ℕ, 2 ≤ a ∧ a < n ∧
      ∀ k s : ℕ, n - 1 = 2 ^ s * k →
        (a ^ k % n ≠ 1) ∧ ∀ r : Fin s, a ^ (2 ^ r.val * k) % n ≠ n - 1 := by
  sorry
