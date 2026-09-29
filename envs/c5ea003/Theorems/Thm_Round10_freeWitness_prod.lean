-- Prove2me | Theorems.Thm_Round10_freeWitness_prod
-- name    : Round10.freeWitness_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:44.060816+00:00
-- url     : https://prove2.me/theorems/0ff4af54-00e2-49b5-96be-baa7d7ed8578
-- title:
--   Squarefree trace lemma.
-- statement:
--   **Squarefree trace lemma.**  For a finite set `P` of distinct primes and
--   `N = ∏_{r ∈ P} r`, the number of `k`-th roots of unity modulo `N` is
--   `∏_{r ∈ P} gcd(r - 1, k)`.
--
--   ```lean
--   theorem Round10.freeWitness_prod(k : ℕ) :
--       ∀ (P : Finset ℕ), (∀ r ∈ P, r.Prime) →
--         freeWitness (∏ r ∈ P, r) k = ∏ r ∈ P, (r - 1).gcd k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/SquarefreeTrace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/SquarefreeTrace.lean#L38

-- Thm stub generated from Geometry/Round10Closures/SquarefreeTrace.lean
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

theorem Round10.freeWitness_prod(k : ℕ) :
    ∀ (P : Finset ℕ), (∀ r ∈ P, r.Prime) →
      freeWitness (∏ r ∈ P, r) k = ∏ r ∈ P, (r - 1).gcd k := by sorry
