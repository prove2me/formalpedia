-- Prove2me | Definitions.Def_Algebra_PosetTheory_FibonacciApparitionSheaf
-- name    : Algebra_PosetTheory_FibonacciApparitionSheaf
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:07:55.64754+00:00
-- url     : https://prove2.me/theorems/bb4bd505-e0c8-4c4f-bb36-d9799bd7e6fe
-- title:
--   Aether Catalog definitions — Algebra_PosetTheory_FibonacciApparitionSheaf
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetTheory.FibonacciApparitionSheaf`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetTheory/FibonacciApparitionSheaf.lean by skeleton subtraction
import Mathlib

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

namespace FibonacciApparitionSheaf

/-- `p` has a rank of apparition when it divides some Fibonacci number of positive index. -/
def HasFibRank (p : ℕ) : Prop := ∃ n, 0 < n ∧ p ∣ Nat.fib n



open Classical in
/-- The rank of apparition of `p`: the least positive `n` with `p ∣ F n`, and `0` when no such
index exists (which happens only for `p = 0`). -/
noncomputable def fibRank (p : ℕ) : ℕ :=
  if h : HasFibRank p then Nat.find h else 0






end FibonacciApparitionSheaf


