-- Prove2me | Theorems.Thm_Round10_prod_eq_prod_of_le
-- name    : Round10.prod_eq_prod_of_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T14:22:03.703357+00:00
-- url     : https://prove2.me/theorems/e6492e70-788d-4638-ac98-e3899f58958f
-- title:
--   Termwise cancellation for products of naturals bounded by positive factors.
-- statement:
--   Termwise cancellation for products of naturals bounded by positive factors.
--
--   ```lean
--   theorem Round10.prod_eq_prod_of_le: ∀ (P : Finset ℕ) (f g : ℕ → ℕ), (∀ i ∈ P, f i ≤ g i) →
--       (∀ i ∈ P, 0 < g i) → ∏ i ∈ P, f i = ∏ i ∈ P, g i → ∀ i ∈ P, f i = g i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/SquarefreeTrace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/SquarefreeTrace.lean#L76

-- Thm stub generated from Geometry/Round10Closures/SquarefreeTrace.lean
import Mathlib
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







/-! ### The Carmichael threshold for squarefree moduli (cycle 4)

The completeness analysis of `AggregationCost.lean` generalises verbatim: a free witness of
a squarefree modulus is maximal exactly at the multiples of `lcm_{r ∈ P} (r-1)`, the
Carmichael exponent of `N`.  So the aggregation depth of the classical channel is the
Carmichael function, for every squarefree modulus and not just for semiprimes. -/

theorem Round10.prod_eq_prod_of_le: ∀ (P : Finset ℕ) (f g : ℕ → ℕ), (∀ i ∈ P, f i ≤ g i) →
    (∀ i ∈ P, 0 < g i) → ∏ i ∈ P, f i = ∏ i ∈ P, g i → ∀ i ∈ P, f i = g i := by sorry
