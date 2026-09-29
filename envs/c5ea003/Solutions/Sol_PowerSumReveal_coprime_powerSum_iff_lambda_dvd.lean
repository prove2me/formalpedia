-- Prove2me | solution 1 for PowerSumReveal.coprime_powerSum_iff_lambda_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:56:43.574616+00:00
-- url     : https://prove2.me/submissions/274ff092-7c4f-440f-bc31-426b2de811f2

-- Sol generated from Geometry/PowerSumSquarefree.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumSquarefree
import Theorems.Thm_PowerSumReveal_prime_dvd_powerSum_iff

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


/-- In a squarefree number, a prime factor appears to the first power only. -/
lemma not_dvd_div_of_squarefree {N p : ℕ} (hN : Squarefree N) (hp : p.Prime) (hd : p ∣ N) :
    ¬ p ∣ N / p := by
  intro h2
  have hsq : p * p ∣ N := by
    obtain ⟨c, hc⟩ := hd
    obtain ⟨d, hdd⟩ := h2
    subst hc
    rw [Nat.mul_div_cancel_left _ hp.pos] at hdd
    exact ⟨d, by rw [hdd]; ring⟩
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hN p hsq))

/-- **Divisibility criterion, squarefree case.**  For squarefree `N`, a prime `p ∣ N`
and `k ≥ 1`: `p ∣ powerSum N k ↔ ¬ (p-1) ∣ k`. -/
theorem prime_dvd_powerSum_iff_squarefree {N p k : ℕ} (hN : Squarefree N) (hp : p.Prime)
    (hd : p ∣ N) (hk : k ≠ 0) :
    p ∣ powerSum N k ↔ ¬ (p - 1) ∣ k := by
  obtain ⟨m, hm⟩ := hd
  have hpm : ¬ p ∣ m := by
    have := not_dvd_div_of_squarefree hN hp ⟨m, hm⟩
    rwa [hm, Nat.mul_div_cancel_left _ hp.pos] at this
  rw [hm]
  exact prime_dvd_powerSum_iff hp hpm hk






open PowerSumReveal in
theorem solution{N k : ℕ} (hN : Squarefree N) (hN0 : N ≠ 0)
    (hk : k ≠ 0) :
    Nat.Coprime (powerSum N k) N ↔ lambdaSqfree N ∣ k := by
  rw [lambdaSqfree, Finset.lcm_dvd_iff]
  constructor
  · intro hcop r hr
    rw [Nat.mem_primeFactors] at hr
    obtain ⟨hrp, hrN, -⟩ := hr
    by_contra hdk
    have hdvd : r ∣ powerSum N k :=
      (prime_dvd_powerSum_iff_squarefree hN hrp hrN hk).2 hdk
    exact Nat.Prime.not_coprime_iff_dvd.2 ⟨r, hrp, hdvd, hrN⟩ hcop
  · intro hall
    by_contra hcop
    obtain ⟨r, hrp, hrS, hrN⟩ := Nat.Prime.not_coprime_iff_dvd.1 hcop
    have hmem : r ∈ N.primeFactors := Nat.mem_primeFactors.2 ⟨hrp, hrN, hN0⟩
    exact (prime_dvd_powerSum_iff_squarefree hN hrp hrN hk).1 hrS (hall r hmem)
