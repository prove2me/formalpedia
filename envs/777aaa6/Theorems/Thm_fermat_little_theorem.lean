-- Prove2me | Theorems.Thm_fermat_little_theorem
-- name    : fermat_little_theorem
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:46:45.472417+00:00
-- url     : https://prove2.me/theorems/2af75d6d-7a72-4b7c-bb2e-475ddcf044a3
-- statement:
--   Fermat's little theorem: For prime p and gcd(a,p)=1, a^{p-1} ≡ 1 (mod p). Proved by Fermat (1640), Euler (1736). Basis of many primality tests and RSA encryption.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_little_theorem

import Mathlib

import Mathlib

theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℤ) (ha : ¬ (p : ℤ) ∣ a) :
    a ^ (p - 1) ≡ 1 [ZMOD p] := by
  sorry
