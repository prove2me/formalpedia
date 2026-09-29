-- Prove2me | Theorems.Thm_PowerSumReveal_pollard_universally_bad_base
-- name    : PowerSumReveal.pollard_universally_bad_base
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:38:17.231085+00:00
-- url     : https://prove2.me/theorems/49917500-5808-4d91-b384-94a88776d47e
-- title:
--   Theorem 2a (a universally bad Pollard base).
-- statement:
--   **Theorem 2a (a universally bad Pollard base).**  Let `N = p * q` with `p ≠ q`
--   distinct odd primes.  Then the nontrivial base `a = N - 1` never reveals a factor:
--   for every exponent `M`, `pollardGcd N (N-1) M` is `N` (when `M` is even) or `1`
--   (when `M` is odd).  In particular it is never a proper divisor of `N`.
--
--   ```lean
--   theorem PowerSumReveal.pollard_universally_bad_base(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
--       (hp2 : p ≠ 2) (hq2 : q ≠ 2) (M : ℕ) :
--       pollardGcd (p * q) (p * q - 1) M = if Even M then p * q else 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PowerSumPollardRobustness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PowerSumPollardRobustness.lean#L68

-- Thm stub generated from Geometry/PowerSumPollardRobustness.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPollardRobustness

/-!
# Robustness: the power sum has no "bad base", Pollard's `p-1` does

Pollard's `p-1` method depends on a *base* `a`: it computes `gcd (a^M - 1, N)` and
succeeds only if the multiplicative order of `a` modulo one prime factor divides the
exponent `M` while the order modulo the other one does not.  The power-sum quantity
`powerSum N k = ∑_{a=1}^{N} a^k` has no base parameter at all: it aggregates every
residue simultaneously.

This file makes the contrast precise.

* `PowerSumReveal.pollard_universally_bad_base` — for a semiprime `N = p*q` of distinct
  *odd* primes, the base `a = N - 1` (a nontrivial base, coprime to `N`) is bad for
  **every** exponent `M ≥ 1`: `gcd (a^M - 1, N) ∈ {1, N}`, never a proper factor.
* `PowerSumReveal.powerSum_succeeds_where_pollard_fails` — at the very exponent
  `k = p - 1` where that base makes Pollard return the useless value `N`, the power
  sum returns the factor `q` (under the standard side condition `(q-1) ∤ (p-1)`).
* `PowerSumReveal.pollard_bad_base_example` — the concrete instance `N = 35`, `M = 4`,
  `a = 6`: Pollard returns `35`, the power sum returns `7`.

Note that the statement `a = N - 1` is a genuinely nontrivial base: `1 < N - 1 < N`.
-/

open PowerSumReveal

open Finset

variable {p q : ℕ}

theorem PowerSumReveal.pollard_universally_bad_base(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (M : ℕ) :
    pollardGcd (p * q) (p * q - 1) M = if Even M then p * q else 1 := by sorry
