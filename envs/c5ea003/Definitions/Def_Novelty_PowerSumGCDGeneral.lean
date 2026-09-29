-- Prove2me | Definitions.Def_Novelty_PowerSumGCDGeneral
-- name    : Novelty_PowerSumGCDGeneral
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:37:06.96487+00:00
-- url     : https://prove2.me/theorems/1d74cdfd-4a93-41ea-b64e-dc51ae2c3313
-- title:
--   Aether Catalog definitions — Novelty_PowerSumGCDGeneral
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.PowerSumGCDGeneral`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/PowerSumGCDGeneral.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDCarmichael

/-!
# The power-sum gcd for arbitrary squarefree moduli, and the first-hit exponent

The semiprime analysis of `Novelty.PowerSumGCDFactoring` and
`Novelty.PowerSumGCDCarmichael` is a shadow of a statement about *every* squarefree
modulus: for `k > 0`,

  `gcd(F(N,k), N) = ∏ { r prime, r ∣ N, (r-1) ∤ k }`.

So the power-sum gcd is a *spectral read-out* of the multiplicative orders in `N`:
it deletes exactly those primes `r` for which `k` is a multiple of `r - 1`.  Its trivial
locus is the multiples of the Carmichael exponent `λ(N) = lcm_{r ∣ N} (r-1)`, and the
power sum itself is periodic mod `N` with that period (Korselt's criterion in disguise).

## Main results

* `gcd_eq_prod_primeFactors_filter` : for squarefree `N`, `gcd(a,N)` is the product of the
  primes of `N` that divide `a`;
* `gcd_powerSum_squarefree` : the product formula displayed above;
* `carmichaelSF` and `gcd_powerSum_eq_one_iff_squarefree` : the trivial locus of the gcd
  is exactly the set of multiples of the Carmichael exponent;
* `modEq_of_forall_prime_modEq` and `powerSum_modEq_add_period_squarefree` : Korselt-type
  periodicity of the power sum for arbitrary squarefree moduli;
* `gcd_powerSum_eq_self_iff`, `gcd_powerSum_eq_self_of_lt_min`,
  `gcd_powerSum_lt_self_at_min` : the *first hit* of the semiprime search happens exactly
  at `k = min(p-1, q-1)`, which is the source of the `O(N^{3/2})` cost of the method.
-/

open Finset

namespace PowerSumGCD



/-- The Carmichael exponent of a squarefree modulus: `lcm` of `r - 1` over the primes
`r ∣ N`. -/
def carmichaelSF (N : ℕ) : ℕ := N.primeFactors.lcm (fun r => r - 1)








end PowerSumGCD


