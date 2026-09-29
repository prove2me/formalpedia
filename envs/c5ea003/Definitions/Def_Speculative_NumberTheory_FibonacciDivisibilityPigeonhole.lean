-- Prove2me | Definitions.Def_Speculative_NumberTheory_FibonacciDivisibilityPigeonhole
-- name    : Speculative_NumberTheory_FibonacciDivisibilityPigeonhole
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:33:37.954215+00:00
-- url     : https://prove2.me/theorems/5ffd866b-695b-4fa2-b123-4f4c962b4b63
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_FibonacciDivisibilityPigeonhole
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.FibonacciDivisibilityPigeonhole`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/FibonacciDivisibilityPigeonhole.lean by skeleton subtraction
import Mathlib
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic

/-!
# Fibonacci-Divisibility Pigeonhole Bridge

This file contains three theorems:

* `fib_dvd_of_dvd`: divisibility of indices implies divisibility of Fibonacci numbers.
* `fib_dvd_iff`: for `3 ≤ m`, `Nat.fib m ∣ Nat.fib n ↔ m ∣ n`.
* `divisibility_pigeonhole`: any `n+1` distinct numbers in `[1, 2n]` contain a
  divisibility pair.
-/



/-- The odd part of a natural number: dividing out all factors of 2. -/
def oddPart (x : ℕ) : ℕ := x / (2 ^ x.factorization 2)


