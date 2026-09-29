-- Prove2me | solution 1 for PowerSumGCD.gcd_powerSum_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:30:31.930147+00:00
-- url     : https://prove2.me/submissions/31f0da9c-634b-4891-8680-0354560db339

-- Sol generated from Novelty/PowerSumGCDFactoring.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Theorems.Thm_PowerSumGCD_gcd_prime_eq
import Theorems.Thm_PowerSumGCD_prime_dvd_powerSum_iff

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
theorem solution{p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hk : 0 < k) :
    Nat.gcd (powerSum (p * q) k) (p * q)
      = (if (p - 1) ∣ k then 1 else p) * (if (q - 1) ∣ k then 1 else q) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have hqp' : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  rw [hcop.gcd_mul _]
  have hP : Nat.gcd (powerSum (p * q) k) p = if (p - 1) ∣ k then 1 else p := by
    rw [gcd_prime_eq hp]
    by_cases h : (p - 1) ∣ k
    · simp [h, (prime_dvd_powerSum_iff hp hpq' hk).not_left.mpr (by simpa using h)]
    · simp [h, (prime_dvd_powerSum_iff hp hpq' hk).mpr h]
  have hQ : Nat.gcd (powerSum (p * q) k) q = if (q - 1) ∣ k then 1 else q := by
    have hcomm : powerSum (p * q) k = powerSum (q * p) k := by rw [Nat.mul_comm]
    rw [hcomm, gcd_prime_eq hq]
    by_cases h : (q - 1) ∣ k
    · simp [h, (prime_dvd_powerSum_iff hq hqp' hk).not_left.mpr (by simpa using h)]
    · simp [h, (prime_dvd_powerSum_iff hq hqp' hk).mpr h]
  rw [hP, hQ]
