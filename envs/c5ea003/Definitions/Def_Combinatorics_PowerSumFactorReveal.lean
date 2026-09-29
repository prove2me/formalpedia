-- Prove2me | Definitions.Def_Combinatorics_PowerSumFactorReveal
-- name    : Combinatorics_PowerSumFactorReveal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:44:45.142378+00:00
-- url     : https://prove2.me/theorems/b30cdad6-d3d9-49d0-8688-8a773e43f6ca
-- title:
--   Aether Catalog definitions — Combinatorics_PowerSumFactorReveal
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.PowerSumFactorReveal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/PowerSumFactorReveal.lean by skeleton subtraction
import Mathlib

/-!
# Power-sum factor reveal for squarefree moduli

For a modulus `N` let
`F(N, k) = ∑_{a = 1}^{N} a ^ k`  (`PowerSumReveal.powerSum`).

The central observation is a **complete local computation**: if `p` is a prime
dividing `N` and `k ≥ 1`, then modulo `p` the interval `{1, …, N}` covers each
residue class exactly `N / p` times, so

`F(N, k) ≡ (N / p) · ∑_{x ∈ ZMod p} x ^ k ≡ (N / p) · (if (p-1) ∣ k then -1 else 0)  (mod p)`.

For squarefree `N` this gives the exact criterion

`p ∣ F(N, k) ↔ ¬ (p - 1) ∣ k`,

hence the exact evaluation of the gcd

`gcd (F(N, k), N) = ∏ { p ∈ N.primeFactors | ¬ (p - 1) ∣ k }`,

which for a semiprime `N = p q` specialises to
`gcd (F(N, k), N) = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`,
and in particular `gcd (F(N, p-1), N) = q` whenever `(q-1) ∤ (p-1)`.

Main results:

* `sum_pow_zmod` — `∑_{x : ZMod p} x ^ k = if (p-1) ∣ k then -1 else 0` for `k ≠ 0`.
* `cast_powerSum` — the local formula for `F(N,k)` modulo a prime divisor of `N`.
* `prime_dvd_powerSum_iff` — `p ∣ F(N,k) ↔ ¬ (p-1) ∣ k` for squarefree `N`.
* `gcd_powerSum_semiprime` — Theorem 1, in exact (all `k`) form.
* `powerSum_reveal` — the factoring corollary at `k = p - 1`.
* `gcd_powerSum_squarefree` — the general squarefree product formula.
* `gcd_powerSum_eq_one_iff` — the gcd is `1` exactly on multiples of the
  Carmichael function `λ(N) = lcm_{p ∣ N} (p-1)`.
-/

namespace PowerSumReveal

open Finset

/-! ## The local sum over `ZMod p` -/





/-! ## The power sum and its local values -/

/-- `F(N, k) = ∑_{a=1}^{N} a ^ k`. -/
def powerSum (N k : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 N, a ^ k





/-! ## The gcd evaluation -/






/-! ## The general squarefree formula -/


/-- The Carmichael-type exponent of a squarefree modulus:
`λ(N) = lcm_{p ∣ N} (p - 1)`. -/
def lam (N : ℕ) : ℕ := N.primeFactors.lcm (fun p => p - 1)


end PowerSumReveal


