-- Prove2me | Definitions.Def_Probability_PolynomialCounting
-- name    : Probability_PolynomialCounting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:16.208771+00:00
-- url     : https://prove2.me/theorems/1df16568-5b88-4357-acfd-e3da1b7e287a
-- title:
--   Aether Catalog definitions — Probability_PolynomialCounting
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PolynomialCounting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PolynomialCounting.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
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

namespace FactoringLab

open Finset

/-! ## 1.  The finite populations -/

/-- The primes that can occur as the *smaller* factor of a semiprime `≤ X`. -/
def smallPrimes (X : ℕ) : Finset ℕ :=
  (Finset.range (Nat.sqrt X + 1)).filter Nat.Prime

/-- All ordered prime pairs `(p, q)`, `p < q`, with `pq ≤ X`: the population of
semiprimes below `X`. -/
def semiprimePairs (X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (X + 1)) ×ˢ (Finset.range (X + 1))).filter
    (fun z => z.1.Prime ∧ z.2.Prime ∧ z.1 < z.2 ∧ z.1 * z.2 ≤ X)

/-- The pairs on which the polynomial `P` *succeeds*: it returns the smaller
prime factor of `N = pq`. -/
def successPairs (P : Polynomial ℚ) (X : ℕ) : Finset (ℕ × ℕ) :=
  (semiprimePairs X).filter (fun z => P.eval ((z.1 * z.2 : ℕ) : ℚ) = (z.1 : ℚ))




/-! ## 2.  The smaller factor of a semiprime below `X` is at most `√X` -/


/-! ## 3.  The fibre bound -/


/-! ## 4.  The global counting barrier -/




/-! ## 5.  The counting barrier for rational functions -/

/-- The pairs on which the rational function `A/B` succeeds: `A(N) = p · B(N)`
for `N = pq`.  (Written multiplicatively, so no nonvanishing hypothesis on `B`
is needed.) -/
def ratSuccessPairs (A B : Polynomial ℚ) (X : ℕ) : Finset (ℕ × ℕ) :=
  (semiprimePairs X).filter
    (fun z => A.eval ((z.1 * z.2 : ℕ) : ℚ) = (z.1 : ℚ) * B.eval ((z.1 * z.2 : ℕ) : ℚ))





end FactoringLab


