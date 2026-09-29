-- Prove2me | solution 1 for PowerSumGCD.powerSum_coprime_iff_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:33:15.151125+00:00
-- url     : https://prove2.me/submissions/78755366-e38c-467c-9cfa-9ba048fd2f13

-- Sol generated from Novelty/PowerSumGCDFactoring.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Theorems.Thm_PowerSumGCD_exists_cofactor_of_squarefree
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
theorem solution{N k : ℕ} (hN : Squarefree N) (hk : 0 < k) :
    Nat.Coprime (powerSum N k) N ↔ ∀ r : ℕ, r.Prime → r ∣ N → (r - 1) ∣ k := by
  constructor
  · intro hcop r hr hrN
    by_contra hdk
    obtain ⟨m, hm, hrm⟩ := exists_cofactor_of_squarefree hN hr hrN
    rw [hm] at hcop
    have hdvdF : r ∣ powerSum (r * m) k := (prime_dvd_powerSum_iff hr hrm hk).mpr hdk
    have hg : r ∣ Nat.gcd (powerSum (r * m) k) (r * m) := Nat.dvd_gcd hdvdF ⟨m, rfl⟩
    rw [hcop] at hg
    exact hr.one_lt.ne' (Nat.dvd_one.mp hg)
  · intro h
    by_contra hcop
    obtain ⟨r, hr, hrF, hrN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    obtain ⟨m, hm, hrm⟩ := exists_cofactor_of_squarefree hN hr hrN
    rw [hm] at hrF
    exact (prime_dvd_powerSum_iff hr hrm hk).mp hrF (h r hr hrN)
