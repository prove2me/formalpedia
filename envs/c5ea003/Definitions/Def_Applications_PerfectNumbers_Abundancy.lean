-- Prove2me | Definitions.Def_Applications_PerfectNumbers_Abundancy
-- name    : Applications_PerfectNumbers_Abundancy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:16.155393+00:00
-- url     : https://prove2.me/theorems/28071e12-0523-4f3f-a425-77da44ff3139
-- title:
--   Aether Catalog definitions — Applications_PerfectNumbers_Abundancy
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PerfectNumbers.Abundancy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PerfectNumbers/Abundancy.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The abundancy index: multiplicativity and divisibility monotonicity

The *abundancy index* of a natural number `n` is the rational number `σ₁(n) / n`,
where `σ₁(n) = ∑_{d ∣ n} d` is the sum-of-divisors function.  It measures how
"abundant" a number is: `n` is perfect exactly when its abundancy index equals `2`.

This file establishes two basic structural facts about the abundancy index:

* **Multiplicativity** (`abundancy_mul_of_coprime`): for coprime `m, n`,
  `abundancy (m * n) = abundancy m * abundancy n`.
* **Divisibility monotonicity** (`abundancy_le_of_dvd`, `abundancy_lt_of_dvd_lt`):
  if `d ∣ n` then `abundancy d ≤ abundancy n`, with strict inequality when `d < n`.

## Breaking the circular dependency

A common pitfall is to prove multiplicativity *via* a monotonicity/embedding
argument and monotonicity *via* multiplicativity, producing a circular development.
Here the two results are proved completely independently:

* Multiplicativity rests only on the multiplicativity of `σ₁` itself
  (`ArithmeticFunction.isMultiplicative_sigma`) together with the field identity
  `mul_div_mul_comm`.
* Monotonicity rests on a *direct* divisor-sum comparison, with no reference to
  multiplicativity or to any coprime factorisation: each divisor `e` of `d` is sent
  to the divisor `e * (n / d)` of `n`.  This map is injective, so the image of
  `d.divisors` is a subset of `n.divisors` whose elementwise sum is exactly
  `(n / d) · σ₁(d)`.  Comparing sums of nonnegative terms gives
  `σ₁(d) · (n / d) ≤ σ₁(n)`, i.e. `σ₁(d) · n ≤ σ₁(n) · d`, which is precisely
  `abundancy d ≤ abundancy n`.  When `d < n` the divisor `1 ∈ n.divisors` is missing
  from the image (its only preimage would require `n / d = 1`), yielding the strict
  inequality.
-/

open ArithmeticFunction Finset

namespace PerfectNumbers

/-- The abundancy index of `n`, namely `σ₁(n) / n` as a rational number.
For `n = 0` this evaluates to `0` by the junk-value convention for division. -/
noncomputable def abundancy (n : ℕ) : ℚ := (ArithmeticFunction.sigma 1 n : ℚ) / (n : ℚ)


/-!
## The core divisor-sum comparison (no multiplicativity used)

The map `e ↦ e * (n / d)` injects `d.divisors` into `n.divisors`.  Summing over the
image and comparing with the full sum over `n.divisors` gives the basic inequality
`σ₁(d) · (n / d) ≤ σ₁(n)`.
-/





/-!
## Divisibility monotonicity of the abundancy index
-/



/-!
## Multiplicativity of the abundancy index
-/


end PerfectNumbers


