-- Prove2me | Definitions.Def_Novelty_PowerSumGCDFactoring
-- name    : Novelty_PowerSumGCDFactoring
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:35:55.454265+00:00
-- url     : https://prove2.me/theorems/8401864e-2114-4cf7-8c2c-cfaa35ff7eab
-- title:
--   Aether Catalog definitions — Novelty_PowerSumGCDFactoring
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.PowerSumGCDFactoring`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/PowerSumGCDFactoring.lean by skeleton subtraction
import Mathlib

/-!
# Power-sum GCD factoring: `gcd(∑_{a=1}^{N} a^k, N)` reveals the prime factors

Let `F(N,k) = ∑_{a=1}^{N} a^k` (`powerSum N k` below).  For a prime `r` dividing
`N` exactly once, the residues `1, …, N` cover each residue class mod `r` the
same number of times, so mod `r` the power sum collapses to a multiple of the
complete power sum `∑_{x : ZMod r} x^k`, which is the classical `-1`/`0`
dichotomy of finite fields.  The upshot is a *complete* characterisation

  `r ∣ F(N,k)  ↔  ¬ (r-1) ∣ k`      (`prime_dvd_powerSum_iff`)

from which the whole "factor reveal" phenomenon follows by elementary gcd
bookkeeping.

## Main results

* `sum_pow_univ_ZMod` : `∑ x : ZMod p, x^k = if (p-1) ∣ k then -1 else 0` for
  `k > 0` (the complete-power-sum dichotomy, including the zero element).
* `cast_powerSum` : `(F(p*q, k) : ZMod p) = q * (if (p-1) ∣ k then -1 else 0)`.
* `prime_dvd_powerSum_iff` : the divisibility characterisation above.
* `gcd_powerSum_semiprime` : for distinct primes `p q` and `k > 0`,
  `gcd (F(pq,k)) (pq) = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`.
* `gcd_powerSum_eq_factor` : **Theorem 1** — if `(q-1) ∤ (p-1)` then
  `gcd (F(pq, p-1)) (pq) = q`, a nontrivial factor of `N = pq`.
* `powerSum_coprime_iff_squarefree` : for squarefree `N`, `F(N,k)` is coprime to
  `N` exactly when every prime `r ∣ N` satisfies `(r-1) ∣ k` — the Carmichael
  condition.
-/

open Finset

namespace PowerSumGCD

/-- The power sum `F(N,k) = ∑_{a=1}^{N} a^k`. -/
def powerSum (N k : ℕ) : ℕ := ∑ a ∈ Finset.Icc 1 N, a ^ k




section CastLemmas

variable {R : Type*} [AddCommMonoid R]



end CastLemmas










end PowerSumGCD


