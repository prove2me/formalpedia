-- Prove2me | Theorems.Thm_wilson_theorem_generalization
-- name    : wilson_theorem_generalization
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:44:51.520145+00:00
-- url     : https://prove2.me/theorems/48c0180e-1682-464a-b262-bba8a8b22a26
-- statement:
--   Wilson's theorem: n is prime iff (n-1)! ≡ -1 (mod n). Proved. Generalizations to Wilson primes (p² | (p-1)!+1) are open: only Wilson primes known are 5, 13, 563.
-- source:
--   https://en.wikipedia.org/wiki/Wilson%27s_theorem

import Mathlib

import Mathlib

theorem wilson_theorem_generalization (n : ℕ) (hn : 2 ≤ n) :
    Nat.Prime n ↔ (n - 1).factorial % n = n - 1 := by
  sorry
