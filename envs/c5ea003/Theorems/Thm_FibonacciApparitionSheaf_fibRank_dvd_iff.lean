-- Prove2me | Theorems.Thm_FibonacciApparitionSheaf_fibRank_dvd_iff
-- name    : FibonacciApparitionSheaf.fibRank_dvd_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:32:34.713896+00:00
-- url     : https://prove2.me/theorems/15ad5eaa-a641-4a74-9c85-59f1817693e1
-- title:
--   Strong divisibility.
-- statement:
--   **Strong divisibility.**  A modulus divides `F n` exactly when its rank of apparition
--   divides `n`.  The forward direction uses `Nat.fib_gcd` together with minimality.
--
--   ```lean
--   theorem FibonacciApparitionSheaf.fibRank_dvd_iff{p : ℕ} (h : HasFibRank p) (n : ℕ) :
--       p ∣ Nat.fib n ↔ fibRank p ∣ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PosetTheory/FibonacciApparitionSheaf.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PosetTheory/FibonacciApparitionSheaf.lean#L110

-- Thm stub generated from Algebra/PosetTheory/FibonacciApparitionSheaf.lean
import Mathlib
import Definitions.Def_Algebra_PosetTheory_FibonacciApparitionSheaf

/-!
# The Fibonacci rank of apparition

For a modulus `p ≥ 1`, the *rank of apparition* (entry point) of `p` is the least positive
index `n` with `p ∣ F n`.  This file provides the general theory used by the Carmichael and
primitive-divisor developments:

* `exists_pos_dvd_fib` — every positive modulus divides some Fibonacci number of positive
  index.  The proof is the classical pigeonhole argument: the pair `(F n, F (n+1))` mod `p`
  takes finitely many values, and the Fibonacci recursion can be run backwards, so the
  initial pair `(0, 1)` recurs.
* `fibRank` — the rank of apparition, defined by `Nat.find` when it exists and `0`
  otherwise, so that it is a total function.
* `fibRank_pos`, `dvd_fib_fibRank`, `fibRank_min` — its defining properties.
* `fibRank_dvd_iff` — the *strong divisibility* characterisation `p ∣ F n ↔ fibRank p ∣ n`,
  a consequence of `Nat.fib_gcd`.
-/

open FibonacciApparitionSheaf

theorem FibonacciApparitionSheaf.fibRank_dvd_iff{p : ℕ} (h : HasFibRank p) (n : ℕ) :
    p ∣ Nat.fib n ↔ fibRank p ∣ n := by sorry
