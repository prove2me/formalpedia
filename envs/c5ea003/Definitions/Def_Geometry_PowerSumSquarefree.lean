-- Prove2me | Definitions.Def_Geometry_PowerSumSquarefree
-- name    : Geometry_PowerSumSquarefree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:50:28.488697+00:00
-- url     : https://prove2.me/theorems/3136e162-77f0-4774-bb50-18799bc324e2
-- title:
--   Aether Catalog definitions — Geometry_PowerSumSquarefree
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PowerSumSquarefree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PowerSumSquarefree.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal

/-!
# The power-sum reveal for arbitrary squarefree moduli, and a Giuga/Korselt bridge

The semiprime analysis of `Geometry.PowerSumFactorReveal` uses nothing about the
number of prime factors: for **any** squarefree `N` and any prime `p ∣ N`,

`p ∣ powerSum N k ↔ ¬ (p - 1) ∣ k`   (`k ≥ 1`).

Consequently `gcd (powerSum N k) N = 1` exactly when `λ(N) ∣ k`, where
`λ(N) = lcm_{p ∣ N} (p - 1)` is the Carmichael function of a squarefree number.
This is the general form of the "Carmichael periodicity" phenomenon.

The last section links this to two classical topics.

* *Fermat/Giuga.*  For a prime `p`, `powerSum p (p-1) ≡ -1 (mod p)`.
* *Korselt.*  A squarefree `N` is a Korselt number (`(p-1) ∣ (N-1)` for all `p ∣ N`,
  the criterion defining Carmichael numbers) **iff** the power-sum gcd at the natural
  exponent `k = N - 1` is trivial.  So Carmichael numbers are precisely the squarefree
  moduli on which the exponent `N-1` gives the method no information.

## Main results

* `PowerSumReveal.prime_dvd_powerSum_iff_squarefree`
* `PowerSumReveal.coprime_powerSum_iff_lambda_dvd`
* `PowerSumReveal.powerSum_prime_eq_neg_one` (Fermat/Giuga direction)
* `PowerSumReveal.korselt_iff_coprime_powerSum`
-/

namespace PowerSumReveal

open Finset

/-- The Carmichael function of a squarefree modulus: `lcm_{p ∣ N} (p - 1)`. -/
def lambdaSqfree (N : ℕ) : ℕ := N.primeFactors.lcm (fun p => p - 1)







end PowerSumReveal


