-- Prove2me | Theorems.Thm_Round10_freeWitness_prod_eq_totient_iff
-- name    : Round10.freeWitness_prod_eq_totient_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:55.927006+00:00
-- url     : https://prove2.me/theorems/bb2d0152-6d9c-4c1e-a018-efc72903e433
-- title:
--   Squarefree completeness criterion.
-- statement:
--   **Squarefree completeness criterion.**  A free witness of `N = ∏_{r ∈ P} r` is maximal
--   exactly at the exponents divisible by every `r - 1`.
--
--   ```lean
--   theorem Round10.freeWitness_prod_eq_totient_iff(k : ℕ) (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime) :
--       freeWitness (∏ r ∈ P, r) k = ∏ r ∈ P, (r - 1) ↔ ∀ r ∈ P, (r - 1) ∣ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/SquarefreeTrace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/SquarefreeTrace.lean#L98

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






/-! ### The Carmichael threshold for squarefree moduli (cycle 4)

The completeness analysis of `AggregationCost.lean` generalises verbatim: a free witness of
a squarefree modulus is maximal exactly at the multiples of `lcm_{r ∈ P} (r-1)`, the
Carmichael exponent of `N`.  So the aggregation depth of the classical channel is the
Carmichael function, for every squarefree modulus and not just for semiprimes. -/

theorem Round10.freeWitness_prod_eq_totient_iff(k : ℕ) (P : Finset ℕ) (hP : ∀ r ∈ P, r.Prime) :
    freeWitness (∏ r ∈ P, r) k = ∏ r ∈ P, (r - 1) ↔ ∀ r ∈ P, (r - 1) ∣ k := by sorry
