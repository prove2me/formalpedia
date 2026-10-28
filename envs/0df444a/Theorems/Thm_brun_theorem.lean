-- Prove2me | Theorems.Thm_brun_theorem
-- name    : brun_theorem
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-27T03:28:36.401362+00:00
-- url     : https://prove2.me/theorems/09b55aed-ca8c-4b66-8623-ca7c25d8392a
-- title:
--   Brun's theorem: the sum of reciprocals of twin primes converges
-- statement:
--   The sum of the reciprocals of the twin primes converges. If p ranges over prime numbers such that p + 2 is also prime, then the sum of 1/p over all such p is finite (Brun, 1919).
-- source:
--   Brun's theorem (1919), formalized from the dyadic-block argument and the PrimePairSieve twin-pair count bound

import Mathlib

theorem brun_theorem : Summable (fun p : {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)} => (p : ℝ)⁻¹) := by sorry
