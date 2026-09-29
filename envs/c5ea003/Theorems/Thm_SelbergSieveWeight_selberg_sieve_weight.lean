-- Prove2me | Theorems.Thm_SelbergSieveWeight_selberg_sieve_weight
-- name    : SelbergSieveWeight.selberg_sieve_weight
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:50:27.438097+00:00
-- url     : https://prove2.me/theorems/354f3ef8-40e8-4007-aee4-b78dca8e0f32
-- title:
--   Selberg sieve weight identity.
-- statement:
--   **Selberg sieve weight identity.** For every positive integer `n`,
--   `μ(n) ^ 2 = ∑_{d^2 ∣ n} μ(d)`.
--
--   ```lean
--   theorem SelbergSieveWeight.selberg_sieve_weight(n : ℕ) (hn : 0 < n) :
--       (moebius n) ^ 2 = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), moebius d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/NumberTheory/SelbergSieveWeight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/NumberTheory/SelbergSieveWeight.lean#L87

-- Thm stub generated from Speculative/NumberTheory/SelbergSieveWeight.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_SelbergSieveWeight
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

open SelbergSieveWeight

theorem SelbergSieveWeight.selberg_sieve_weight(n : ℕ) (hn : 0 < n) :
    (moebius n) ^ 2 = ∑ d ∈ n.divisors.filter (fun d => d ^ 2 ∣ n), moebius d := by sorry
