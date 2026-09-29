-- Prove2me | solution 2 for Round10.prod_eq_prod_of_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-20T01:06:47.831975+00:00
-- url     : https://prove2.me/submissions/c97db0f4-e6b7-4b3c-960b-9a9c2a38e576

-- Sol generated from Geometry/Round10Closures/SquarefreeTrace.lean
import Mathlib
import Theorems.Thm_Round10_eq_of_mul_eq_mul_le
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
theorem solution: ∀ (P : Finset ℕ) (f g : ℕ → ℕ), (∀ i ∈ P, f i ≤ g i) →
    (∀ i ∈ P, 0 < g i) → ∏ i ∈ P, f i = ∏ i ∈ P, g i → ∀ i ∈ P, f i = g i := by
  classical
  intro P
  induction P using Finset.induction with
  | empty => intro _ _ _ _ _ i hi; exact absurd hi (Finset.notMem_empty i)
  | insert a P ha ih =>
      intro f g hle hpos hprod
      rw [Finset.prod_insert ha, Finset.prod_insert ha] at hprod
      have hlep : ∏ i ∈ P, f i ≤ ∏ i ∈ P, g i :=
        Finset.prod_le_prod' fun i hi => hle i (Finset.mem_insert_of_mem hi)
      have hposp : 0 < ∏ i ∈ P, g i :=
        Finset.prod_pos fun i hi => hpos i (Finset.mem_insert_of_mem hi)
      obtain ⟨h1, h2⟩ := eq_of_mul_eq_mul_le (hle a (Finset.mem_insert_self a P)) hlep
        (hpos a (Finset.mem_insert_self a P)) hposp hprod
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hiP
      · exact h1
      · exact ih f g (fun j hj => hle j (Finset.mem_insert_of_mem hj))
          (fun j hj => hpos j (Finset.mem_insert_of_mem hj)) h2 i hiP
