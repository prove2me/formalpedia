-- Prove2me | Theorems.Thm_divisibility_pigeonhole
-- name    : divisibility_pigeonhole
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:54:47.591553+00:00
-- url     : https://prove2.me/theorems/4d4f4298-d791-4951-a814-de206da6e121
-- title:
--   Pigeonhole: any `n+1` distinct numbers in `[1, 2n]` contain a divisibility pair.
-- statement:
--   Pigeonhole: any `n+1` distinct numbers in `[1, 2n]` contain a divisibility pair.
--
--   The hypothesis `hn : n ≥ 1` is retained because it was part of the requested
--   statement, but it is not actually needed for the proof.
--
--   ```lean
--   theorem divisibility_pigeonhole(n : ℕ) (S : Finset ℕ) (hn : n ≥ 1)
--       (hcard : S.card = n + 1) (hsub : S ⊆ Finset.Icc 1 (2 * n)) :
--       ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/NumberTheory/FibonacciDivisibilityPigeonhole.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/NumberTheory/FibonacciDivisibilityPigeonhole.lean#L39

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

theorem divisibility_pigeonhole(n : ℕ) (S : Finset ℕ) (hn : n ≥ 1)
    (hcard : S.card = n + 1) (hsub : S ⊆ Finset.Icc 1 (2 * n)) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b := by sorry
