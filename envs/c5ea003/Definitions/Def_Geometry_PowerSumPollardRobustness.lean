-- Prove2me | Definitions.Def_Geometry_PowerSumPollardRobustness
-- name    : Geometry_PowerSumPollardRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:50:07.190813+00:00
-- url     : https://prove2.me/theorems/5a90b879-0ed0-4496-bfea-ab1a2516058d
-- title:
--   Aether Catalog definitions — Geometry_PowerSumPollardRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PowerSumPollardRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PowerSumPollardRobustness.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal

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

namespace PowerSumReveal

open Finset

variable {p q : ℕ}

/-- Pollard `p-1` style gcd for base `a` and exponent `M`. -/
def pollardGcd (N a M : ℕ) : ℕ := Nat.gcd (a ^ M - 1) N








end PowerSumReveal


