-- Prove2me | Theorems.Thm_fib_dvd_iff
-- name    : fib_dvd_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:54:53.910902+00:00
-- url     : https://prove2.me/theorems/bd311f36-a690-4bdb-907f-794adef968d6
-- title:
--   For `3 ≤ m`, `Nat.fib m ∣ Nat.fib n ↔ m ∣ n`.
-- statement:
--   For `3 ≤ m`, `Nat.fib m ∣ Nat.fib n ↔ m ∣ n`.
--
--   ```lean
--   theorem fib_dvd_iff{m n : ℕ} (hm : 3 ≤ m) : Nat.fib m ∣ Nat.fib n ↔ m ∣ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/NumberTheory/FibonacciDivisibilityPigeonhole.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/NumberTheory/FibonacciDivisibilityPigeonhole.lean#L19

-- Thm stub generated from Speculative/NumberTheory/FibonacciDivisibilityPigeonhole.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_FibonacciDivisibilityPigeonhole
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

theorem fib_dvd_iff{m n : ℕ} (hm : 3 ≤ m) : Nat.fib m ∣ Nat.fib n ↔ m ∣ n := by sorry
