-- Prove2me | solution 1 for PowerSumReveal.gcd_powerSum_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:50:01.607449+00:00
-- url     : https://prove2.me/submissions/1c2157ea-057b-4919-a745-b6c8417de634

-- Sol generated from Geometry/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_gcd_prime_eq
import Theorems.Thm_PowerSumReveal_prime_dvd_powerSum_iff

/-!
# Power-sum GCD factor reveal

For a modulus `N` put

`powerSum N k = ∑_{a = 1}^{N} a ^ k`.

The main result of this file is a *complete* description of `gcd (powerSum N k) N`
when `N = p * q` is a semiprime and `k ≥ 1`:

`gcd (powerSum (p*q) k, p*q) = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`.

The mechanism is a two-step reduction.

* *Periodicity.* The interval `[1, N]` with `N = p * m` covers every residue class
  modulo `p` exactly `m` times, so `powerSum (p*m) k ≡ m * ∑_{x ∈ ZMod p} x^k (mod p)`.
* *Fermat.* For `k ≥ 1`, `∑_{x ∈ ZMod p} x^k = -1` if `(p-1) ∣ k` and `= 0` otherwise.

Consequently `p ∣ powerSum (p*m) k ↔ ¬ (p-1) ∣ k` (when `p ∤ m`), and the gcd formula
follows from multiplicativity of `Nat.gcd` over coprime factors.

Specialising to `k = p - 1` gives the advertised **factor reveal**:
`gcd (powerSum (p*q) (p-1), p*q) = q` whenever `(q-1) ∤ (p-1)`.

## Main results

* `PowerSumReveal.sum_pow_zmod` — Fermat power-sum over `ZMod p`.
* `PowerSumReveal.powerSum_cast` — the periodicity reduction, in `ZMod p`.
* `PowerSumReveal.prime_dvd_powerSum_iff` — divisibility criterion.
* `PowerSumReveal.gcd_powerSum_semiprime` — the master gcd formula.
* `PowerSumReveal.powerSum_factor_reveal` — Theorem 1 (factor reveal at `k = p-1`).
-/

open PowerSumReveal

open Finset



/-! ## Step 1: the Fermat power sum over `ZMod p` -/


/-! ## Step 2: periodicity of `a ↦ a mod p` on an interval of length `p * m` -/





/-! ## Step 3: the divisibility criterion -/


/-! ## Step 4: the gcd formula -/



/-! ## Theorem 1: the factor reveal -/





open PowerSumReveal in
theorem solution{p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hk : k ≠ 0) :
    Nat.gcd (powerSum (p * q) k) (p * q)
      = (if (p - 1) ∣ k then 1 else p) * (if (q - 1) ∣ k then 1 else q) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hqp : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
  have hpq' : ¬ q ∣ p := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 h).symm
  have hP : p ∣ powerSum (p * q) k ↔ ¬ (p - 1) ∣ k := prime_dvd_powerSum_iff hp hqp hk
  have hQ : q ∣ powerSum (p * q) k ↔ ¬ (q - 1) ∣ k := by
    have := prime_dvd_powerSum_iff hq hpq' hk
    rwa [mul_comm q p] at this
  rw [Nat.Coprime.gcd_mul _ hcop, gcd_prime_eq hp, gcd_prime_eq hq]
  by_cases h1 : (p - 1) ∣ k <;> by_cases h2 : (q - 1) ∣ k <;>
    simp [h1, h2, hP, hQ]
