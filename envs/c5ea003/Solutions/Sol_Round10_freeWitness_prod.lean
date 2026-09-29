-- Prove2me | solution 1 for Round10.freeWitness_prod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:52:45.178765+00:00
-- url     : https://prove2.me/submissions/7acef245-9836-4a36-b7e5-3bcccc0cb7e5

-- Sol generated from Geometry/Round10Closures/SquarefreeTrace.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
import Theorems.Thm_Round10_card_units_zmod_prime
import Theorems.Thm_Round10_freeWitness_mul
import Theorems.Thm_Round10_freeWitness_one
import Theorems.Thm_Round10_rootCount_of_isCyclic
/-
Round-10 Closures — Part VIII (cycle 3): the trace lemma beyond semiprimes.

Cycle 3 pushes the classification off the semiprime case: the free-witness family is
multiplicative, so for every squarefree modulus `N = ∏_{r ∈ P} r` (a finite set of distinct
primes) the witness is the product of the local gcd-residue coordinates,

    R_k(N) = ∏_{r ∈ P} gcd(k, r - 1).

Two consequences are recorded:

* the population of square roots of unity is `2^ω(N)` for odd squarefree `N`, so the
  residue coordinate *counts the prime factors* — the classified coordinate already knows
  `ω(N)`, while it still cannot name a single factor without aggregation;
* the witness of the exponent `k` is still bounded by `k^{ω(N)}`, so the bounded-exponent
  barrier of `JointClosure.lean` degrades only polynomially in the number of factors.
-/

open Round10



/-- The local factor at a prime. -/
theorem freeWitness_prime (r k : ℕ) [Fact r.Prime] :
    freeWitness r k = (r - 1).gcd k := by
  rw [freeWitness, rootCount_of_isCyclic, card_units_zmod_prime]



/-! ### The Carmichael threshold for squarefree moduli (cycle 4)

The completeness analysis of `AggregationCost.lean` generalises verbatim: a free witness of
a squarefree modulus is maximal exactly at the multiples of `lcm_{r ∈ P} (r-1)`, the
Carmichael exponent of `N`.  So the aggregation depth of the classical channel is the
Carmichael function, for every squarefree modulus and not just for semiprimes. -/






open Round10 in
theorem solution(k : ℕ) :
    ∀ (P : Finset ℕ), (∀ r ∈ P, r.Prime) →
      freeWitness (∏ r ∈ P, r) k = ∏ r ∈ P, (r - 1).gcd k := by
  classical
  intro P
  induction P using Finset.induction with
  | empty => intro _; simpa using freeWitness_one k
  | insert r P hr ih =>
      intro hP
      haveI : Fact (r.Prime) := ⟨hP r (Finset.mem_insert_self r P)⟩
      have hPprime : ∀ s ∈ P, s.Prime := fun s hs => hP s (Finset.mem_insert_of_mem hs)
      have hcop : Nat.Coprime r (∏ s ∈ P, s) :=
        Nat.Coprime.prod_right fun s hs =>
          (Nat.coprime_primes (Fact.out) (hPprime s hs)).mpr (by rintro rfl; exact hr hs)
      rw [Finset.prod_insert hr, Finset.prod_insert hr, freeWitness_mul hcop,
        freeWitness_prime r k, ih hPprime]
