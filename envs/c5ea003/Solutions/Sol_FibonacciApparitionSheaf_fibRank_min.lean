-- Prove2me | solution 1 for FibonacciApparitionSheaf.fibRank_min
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:01:44.993099+00:00
-- url     : https://prove2.me/submissions/28e4d7eb-8f4b-4cf5-86a7-d858dba60956

-- Sol generated from Algebra/PosetTheory/FibonacciApparitionSheaf.lean
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





theorem fibRank_eq_find {p : ℕ} (h : HasFibRank p) :
    fibRank p = Nat.find h := by
  rw [fibRank, dif_pos h]






open FibonacciApparitionSheaf in
theorem solution{p k : ℕ} (hk : 0 < k) (hlt : k < fibRank p) : ¬ p ∣ Nat.fib k := by
  intro hdvd
  have h : HasFibRank p := ⟨k, hk, hdvd⟩
  rw [fibRank_eq_find h] at hlt
  exact Nat.find_min h hlt ⟨hk, hdvd⟩
