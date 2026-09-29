-- Prove2me | solution 1 for PowerSumReveal.korselt_iff_coprime_powerSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:04:37.701618+00:00
-- url     : https://prove2.me/submissions/d7aa38fd-8ae2-4554-8a7a-eea8a4e2b091

-- Sol generated from Geometry/PowerSumSquarefree.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumSquarefree
import Theorems.Thm_PowerSumReveal_coprime_powerSum_iff_lambda_dvd

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

open PowerSumReveal

open Finset









open PowerSumReveal in
theorem solution{N : ℕ} (hN : Squarefree N) (hN2 : 2 ≤ N) :
    (∀ p ∈ N.primeFactors, (p - 1) ∣ (N - 1)) ↔
      Nat.gcd (powerSum N (N - 1)) N = 1 := by
  have hk : N - 1 ≠ 0 := by omega
  have h := coprime_powerSum_iff_lambda_dvd hN (by omega) hk
  rw [Nat.Coprime] at h
  rw [h, lambdaSqfree, Finset.lcm_dvd_iff]
