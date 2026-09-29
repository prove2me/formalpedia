-- Prove2me | solution 1 for FibonacciApparitionSheaf.fibRank_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:05:22.697686+00:00
-- url     : https://prove2.me/submissions/f6c7715b-43e0-4880-91a1-8806c6c8b91f

-- Sol generated from Algebra/PosetTheory/FibonacciApparitionSheaf.lean
import Mathlib
import Definitions.Def_Algebra_PosetTheory_FibonacciApparitionSheaf
import Theorems.Thm_FibonacciApparitionSheaf_dvd_fib_fibRank
import Theorems.Thm_FibonacciApparitionSheaf_fibRank_min
import Theorems.Thm_FibonacciApparitionSheaf_fibRank_pos

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











open FibonacciApparitionSheaf in
theorem solution{p : ℕ} (h : HasFibRank p) (n : ℕ) :
    p ∣ Nat.fib n ↔ fibRank p ∣ n := by
  constructor
  · intro hdvd
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact dvd_zero _
    · have hgcd : p ∣ Nat.fib (Nat.gcd n (fibRank p)) := by
        rw [Nat.fib_gcd]
        exact Nat.dvd_gcd hdvd (dvd_fib_fibRank h)
      have hle : Nat.gcd n (fibRank p) ≤ fibRank p :=
        Nat.le_of_dvd (fibRank_pos h) (Nat.gcd_dvd_right _ _)
      have hgpos : 0 < Nat.gcd n (fibRank p) := Nat.gcd_pos_of_pos_left _ hn
      have heq : Nat.gcd n (fibRank p) = fibRank p := by
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact absurd hgcd (fibRank_min hgpos hlt)
        · exact heq
      exact heq ▸ Nat.gcd_dvd_left _ _
  · intro hdvd
    exact dvd_trans (dvd_fib_fibRank h) (Nat.fib_dvd _ _ hdvd)
