-- Prove2me | solution 1 for PowerSumGCD.prime_dvd_powerSum_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:28:41.39949+00:00
-- url     : https://prove2.me/submissions/add97de6-4580-447f-82d4-bfbe65ab4832

-- Sol generated from Novelty/PowerSumGCDFactoring.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Theorems.Thm_PowerSumGCD_cast_powerSum

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

open PowerSumGCD






variable {R : Type*} [AddCommMonoid R]














open PowerSumGCD in
theorem solution{p q k : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ q) (hk : 0 < k) :
    p ∣ powerSum (p * q) k ↔ ¬ (p - 1) ∣ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcast := cast_powerSum p q hk
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).mp h)
  constructor
  · intro hdvd hdk
    rw [if_pos hdk, mul_neg_one] at hcast
    have h3 : ((powerSum (p * q) k : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [h3] at hcast
    exact hq0 (neg_eq_zero.mp hcast.symm)
  · intro hdk
    rw [if_neg hdk, mul_zero] at hcast
    exact (ZMod.natCast_eq_zero_iff _ _).mp hcast
