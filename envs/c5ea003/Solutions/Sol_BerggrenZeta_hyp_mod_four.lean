-- Prove2me | solution 1 for BerggrenZeta.hyp_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:40:34.253296+00:00
-- url     : https://prove2.me/submissions/709be3da-4334-479d-9834-4293049f344f

-- Sol generated from Novelty/BerggrenTreePrimeHypotenuse.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaAbscissa
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# Prime hypotenuses in the Berggren tree

Which primes occur as hypotenuses of nodes of the Berggren tree?  Since the nodes are
exactly the Euclid seeds (`seedEquiv`) and `c = m² + n²` with `m + n` odd and
`gcd (m,n) = 1`, the answer is governed by Fermat's two-square theorem:

* `hyp_mod_four` — **every** hypotenuse in the tree is `≡ 1 (mod 4)`;
* `prime_hyp_iff` — a prime is the hypotenuse of some node **iff** it is `≡ 1 (mod 4)`;
* `infinite_prime_hyp` — hence, by Dirichlet's theorem, infinitely many nodes of the tree
  carry a prime hypotenuse;
* `summable_primeNode_zeta` — the prime-node Dirichlet series `∑_{c(w) prime} c(w)^{-s}`
  converges for `s > 1`, and
* `primeNode_zeta_ge_primeSum` — it dominates the `χ₄`-restricted prime zeta function
  `∑_{p ≡ 1 (4)} p^{-s}`.

Consequently the "prime number theorem for the Berggren tree" is *not* a new analytic
phenomenon: the prime-hypotenuse counting function of the tree is the counting function of
the primes in the arithmetic progression `1 mod 4`, so an error term of square-root quality
for it is precisely the classical Riemann Hypothesis for the Dirichlet `L`-function
`L(s, χ₄)`.  The Berggren tree therefore transports, but does not simplify, the prime
distribution problem; what it *does* possess unconditionally is the silver critical line of
`Novelty.BerggrenTreeCriticalLine`.
-/

open BerggrenZeta








open BerggrenZeta in
theorem solution(w : List (Fin 3)) : hyp w % 4 = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := seed_isSeed w
  have key : hyp w = (seed w).1 ^ 2 + (seed w).2 ^ 2 := rfl
  rcases Nat.even_or_odd (seed w).1 with ⟨a, ha⟩ | ⟨a, ha⟩
  · -- `m` even, hence `n` odd
    obtain ⟨b, hb⟩ : ∃ b, (seed w).2 = 2 * b + 1 := ⟨(seed w).2 / 2, by omega⟩
    have hval : hyp w = 4 * (a ^ 2 + b ^ 2 + b) + 1 := by
      rw [key, ha, hb]; ring
    omega
  · -- `m` odd, hence `n` even
    obtain ⟨b, hb⟩ : ∃ b, (seed w).2 = 2 * b := ⟨(seed w).2 / 2, by omega⟩
    have hval : hyp w = 4 * (a ^ 2 + a + b ^ 2) + 1 := by
      rw [key, ha, hb]; ring
    omega
