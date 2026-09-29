-- Prove2me | Theorems.Thm_BerggrenZeta_primeNode_zeta_ge_primeSum
-- name    : BerggrenZeta.primeNode_zeta_ge_primeSum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-14T01:24:04.466461+00:00
-- url     : https://prove2.me/theorems/ab46c642-f773-4487-90e3-054cb2759e48
-- title:
--   The prime-node series dominates the `χ₄`-restricted prime zeta `∑_{p ≡ 1 (4)} p^{-s}`:
-- statement:
--   The prime-node series dominates the `χ₄`-restricted prime zeta `∑_{p ≡ 1 (4)} p^{-s}`:
--   choosing, for each prime `p ≡ 1 mod 4`, a node with hypotenuse `p` gives an injection of
--   that set of primes into the prime nodes of the tree.
--
--   ```lean
--   theorem BerggrenZeta.primeNode_zeta_ge_primeSum{s : ℝ} (hs : 1 < s)
--       (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 1) :
--       ∑ p ∈ P, (p : ℝ) ^ (-s) ≤
--         ∑' w : List (Fin 3), (if (hyp w).Prime then (hyp w : ℝ) ^ (-s) else 0) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BerggrenTreePrimeHypotenuse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BerggrenTreePrimeHypotenuse.lean#L146

-- Thm stub generated from Novelty/BerggrenTreePrimeHypotenuse.lean
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

theorem BerggrenZeta.primeNode_zeta_ge_primeSum{s : ℝ} (hs : 1 < s)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ p % 4 = 1) :
    ∑ p ∈ P, (p : ℝ) ^ (-s) ≤
      ∑' w : List (Fin 3), (if (hyp w).Prime then (hyp w : ℝ) ^ (-s) else 0) := by sorry
