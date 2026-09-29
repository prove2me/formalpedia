-- Prove2me | Definitions.Def_Speculative_NumberTheory_SelbergSieveWeight
-- name    : Speculative_NumberTheory_SelbergSieveWeight
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:22.626678+00:00
-- url     : https://prove2.me/theorems/0d88da59-65db-454e-b170-0c9997364aba
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_SelbergSieveWeight
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.SelbergSieveWeight`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/SelbergSieveWeight.lean by skeleton subtraction
import Mathlib
/-
# Selberg sieve weight identity

This module proves the combinatorial identity underlying the Selberg sieve weights:
for every positive integer `n`,
$$\mu^2(n) = \sum_{d^2 \mid n} \mu(d),$$
where `μ` is the Möbius function.

The proof proceeds by introducing the *square-root part* `sqrtPart n`, the largest
integer `m` such that `m^2 ∣ n` (equivalently the number whose `p`-adic valuation is
`⌊v_p(n)/2⌋`).  The key observations are:

* `d ^ 2 ∣ n ↔ d ∣ sqrtPart n` (`dvd_sq_iff`), so the divisors `d` with `d^2 ∣ n`
  are exactly the divisors of `sqrtPart n`;
* `∑_{d ∣ m} μ(d) = if m = 1 then 1 else 0` (Möbius inversion of the constant
  function `1`, via `moebius_mul_coe_zeta`);
* `Squarefree n ↔ sqrtPart n = 1` (`squarefree_iff_sqrtPart`), matching the value of
  `μ^2(n)` given by `moebius_sq`.

Only the definition and basic properties of `μ` and prime factorizations are used; no
results about prime distribution (π(x), Chebyshev bounds, etc.) enter the argument.
-/

open ArithmeticFunction

namespace SelbergSieveWeight

/-- The square-root part of `n`: the integer whose `p`-adic valuation is `⌊v_p(n) / 2⌋`.
This is the largest `m` with `m ^ 2 ∣ n`. -/
noncomputable def sqrtPart (n : ℕ) : ℕ :=
  (n.factorization.mapRange (· / 2) (Nat.zero_div 2)).prod (· ^ ·)






end SelbergSieveWeight


