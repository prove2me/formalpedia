-- Prove2me | Theorems.Thm_FibonacciApparitionSheaf_exists_pos_dvd_fib
-- name    : FibonacciApparitionSheaf.exists_pos_dvd_fib
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:32:24.930756+00:00
-- url     : https://prove2.me/theorems/3b8c4015-8738-41d8-bcbf-450ff90853e8
-- title:
--   Every positive modulus divides a Fibonacci number of positive index.
-- statement:
--   **Every positive modulus divides a Fibonacci number of positive index.**
--
--   The pairs `(F n, F (n+1))` in `ZMod p × ZMod p` cannot be pairwise distinct, and the
--   recursion `F (n+2) = F n + F (n+1)` determines `F n` from the later pair, so a repetition can
--   be pushed back to index `0`; there `F 0 = 0`.
--
--   ```lean
--   theorem FibonacciApparitionSheaf.exists_pos_dvd_fib(p : ℕ) (hp : 0 < p) : ∃ k, 0 < k ∧ p ∣ Nat.fib k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/PosetTheory/FibonacciApparitionSheaf.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/PosetTheory/FibonacciApparitionSheaf.lean#L25

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

theorem FibonacciApparitionSheaf.exists_pos_dvd_fib(p : ℕ) (hp : 0 < p) : ∃ k, 0 < k ∧ p ∣ Nat.fib k := by sorry
