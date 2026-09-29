-- Prove2me | Theorems.Thm_FibonacciApparitionSheaf_hasFibRank_of_pos
-- name    : FibonacciApparitionSheaf.hasFibRank_of_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:32:38.850689+00:00
-- url     : https://prove2.me/theorems/f2a3b907-6221-4e12-8177-4969132a0f87
-- title:
--   Every positive modulus has a rank of apparition.
-- statement:
--   Every positive modulus has a rank of apparition.
--
--   ```lean
--   theorem FibonacciApparitionSheaf.hasFibRank_of_pos(p : ℕ) (hp : 0 < p) : HasFibRank p := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PosetTheory/FibonacciApparitionSheaf.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PosetTheory/FibonacciApparitionSheaf.lean#L80

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

theorem FibonacciApparitionSheaf.hasFibRank_of_pos(p : ℕ) (hp : 0 < p) : HasFibRank p := by sorry
