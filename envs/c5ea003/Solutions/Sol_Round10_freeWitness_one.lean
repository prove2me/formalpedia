-- Prove2me | solution 1 for Round10.freeWitness_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:47:23.626771+00:00
-- url     : https://prove2.me/submissions/406b2f26-743d-4cb6-96e8-ffb20be334ed

-- Sol generated from Geometry/Round10Closures/SquarefreeTrace.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
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






/-! ### The Carmichael threshold for squarefree moduli (cycle 4)

The completeness analysis of `AggregationCost.lean` generalises verbatim: a free witness of
a squarefree modulus is maximal exactly at the multiples of `lcm_{r ∈ P} (r-1)`, the
Carmichael exponent of `N`.  So the aggregation depth of the classical channel is the
Carmichael function, for every squarefree modulus and not just for semiprimes. -/






open Round10 in
theorem solution(k : ℕ) : freeWitness 1 k = 1 := by
  rw [freeWitness, rootCount, Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, ⟨⟨1, one_pow k⟩⟩⟩
