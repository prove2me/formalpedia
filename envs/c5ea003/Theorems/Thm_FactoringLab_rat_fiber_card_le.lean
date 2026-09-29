-- Prove2me | Theorems.Thm_FactoringLab_rat_fiber_card_le
-- name    : FactoringLab.rat_fiber_card_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:33:24.385158+00:00
-- url     : https://prove2.me/theorems/7166c48a-932b-411d-8399-b9732c51284c
-- title:
--   Fibre bound for a rational function: over a fixed small factor `p`, the
-- statement:
--   Fibre bound for a rational function: over a fixed small factor `p`, the
--   successes of `A/B` inject into the roots of the nonzero polynomial
--   `A − p·B`, of degree at most `max (deg A) (deg B)`.
--
--   ```lean
--   theorem FactoringLab.rat_fiber_card_le(A B : Polynomial ℚ) (X : ℕ) (p : ℕ)
--       (hp : p ∈ smallPrimes X) (hAB : A ≠ Polynomial.C (p : ℚ) * B) :
--       {z ∈ ratSuccessPairs A B X | z.1 = p}.card ≤ max A.natDegree B.natDegree := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PolynomialCounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PolynomialCounting.lean#L160

-- Thm stub generated from Probability/PolynomialCounting.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
import Definitions.Def_Probability_PolynomialCounting
/-
# The Global Polynomial Counting Barrier (Factoring Lab, Phase A v19c — cycle 2)

Closing the **global** half of **Conjecture 1** of `FUTURE_DIRECTIONS.md`.

The previous cycle proved the *per-small-factor* bound
`FactoringLab.polynomial_barrier_counting`: for a fixed prime `p`, a polynomial
`P ∈ ℚ[X]` with `P ≠ C p` returns the correct factor `P(pq) = p` for at most
`deg P` primes `q`.  What was left open was the summation over `p` — the global
count of semiprimes `N = pq ≤ X` on which a fixed polynomial succeeds.

This file closes that step.  The main results are:

* `FactoringLab.successPairs_card_le` — for every `P` with `deg P ≥ 1`,
  the number of pairs `(p, q)` of primes with `p < q`, `pq ≤ X` and
  `P(pq) = p` is at most `deg P · π(√X)`, where `π(√X)` is counted by the
  explicit finset `FactoringLab.smallPrimes X`;
* `FactoringLab.successPairs_card_le_sqrt` — the cruder, hypothesis-free form
  `deg P · (√X + 1)`;
* `FactoringLab.exists_polynomial_failure` — the counting bound turned into an
  existence statement: as soon as the number of semiprimes below `X` exceeds
  `deg P · (√X + 1)`, an explicit semiprime on which `P` fails must exist.  In
  particular the *success density* of any fixed polynomial is `O(√X)` against a
  population of order `X log log X / log X`.

The mechanism is exactly the one predicted in the conjecture: the fibre of the
success set over a fixed small factor `p` injects into the root set of
`P − C p`, and the small factor of a semiprime `≤ X` is at most `√X`.
-/

open FactoringLab

open Finset

/-! ## 1.  The finite populations -/







/-! ## 2.  The smaller factor of a semiprime below `X` is at most `√X` -/


/-! ## 3.  The fibre bound -/


/-! ## 4.  The global counting barrier -/




/-! ## 5.  The counting barrier for rational functions -/

theorem FactoringLab.rat_fiber_card_le(A B : Polynomial ℚ) (X : ℕ) (p : ℕ)
    (hp : p ∈ smallPrimes X) (hAB : A ≠ Polynomial.C (p : ℚ) * B) :
    {z ∈ ratSuccessPairs A B X | z.1 = p}.card ≤ max A.natDegree B.natDegree := by sorry
