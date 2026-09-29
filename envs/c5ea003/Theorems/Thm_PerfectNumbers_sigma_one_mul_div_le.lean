-- Prove2me | Theorems.Thm_PerfectNumbers_sigma_one_mul_div_le
-- name    : PerfectNumbers.sigma_one_mul_div_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:59:02.520485+00:00
-- url     : https://prove2.me/theorems/36594d66-07ca-41e1-aaab-e81ecbbf0272
-- title:
--   Scaled embedding of divisor sums.
-- statement:
--   **Scaled embedding of divisor sums.** If `d ∣ n`, then `σ₁(d) · (n / d) ≤ σ₁(n)`.
--
--   The proof embeds `d.divisors` into `n.divisors` via `e ↦ e * (n / d)` and compares
--   sums of nonnegative terms; it does *not* use any multiplicativity of `σ₁`.
--
--   ```lean
--   theorem PerfectNumbers.sigma_one_mul_div_le{d n : ℕ} (hdn : d ∣ n) :
--       sigma 1 d * (n / d) ≤ sigma 1 n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/PerfectNumbers/Abundancy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/PerfectNumbers/Abundancy.lean#L57

-- Thm stub generated from Applications/PerfectNumbers/Abundancy.lean
import Mathlib
import Definitions.Def_Applications_PerfectNumbers_Abundancy
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

open PerfectNumbers



/-!
## The core divisor-sum comparison (no multiplicativity used)

The map `e ↦ e * (n / d)` injects `d.divisors` into `n.divisors`.  Summing over the
image and comparing with the full sum over `n.divisors` gives the basic inequality
`σ₁(d) · (n / d) ≤ σ₁(n)`.
-/

theorem PerfectNumbers.sigma_one_mul_div_le{d n : ℕ} (hdn : d ∣ n) :
    sigma 1 d * (n / d) ≤ sigma 1 n := by sorry
