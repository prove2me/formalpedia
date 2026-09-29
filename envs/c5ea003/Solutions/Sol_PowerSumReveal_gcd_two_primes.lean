-- Prove2me | solution 1 for PowerSumReveal.gcd_two_primes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:12:13.625554+00:00
-- url     : https://prove2.me/submissions/e4839fef-583f-4d98-af12-7d7bbe743d97

-- Sol generated from Combinatorics/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal

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

open PowerSumReveal

open Finset

/-! ## The local sum over `ZMod p` -/





/-! ## The power sum and its local values -/






/-! ## The gcd evaluation -/






/-! ## The general squarefree formula -/





open PowerSumReveal in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (m : ℕ) :
    Nat.gcd m (p * q) = (if p ∣ m then p else 1) * (if q ∣ m then q else 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  by_cases hpm : p ∣ m <;> by_cases hqm : q ∣ m
  · have hdvd : p * q ∣ m := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpm hqm
    simp [hpm, hqm, Nat.gcd_eq_right hdvd]
  · have hcq : Nat.Coprime m q := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqm |>.symm
    have h1 : Nat.gcd m (p * q) = Nat.gcd m p := Nat.gcd_mul_left_right_of_gcd_eq_one hcq
    simp [hpm, hqm, h1, Nat.gcd_eq_right hpm]
  · have hcp : Nat.Coprime m p := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm |>.symm
    have h1 : Nat.gcd m (p * q) = Nat.gcd m q :=
      Nat.Coprime.gcd_mul_left_cancel_right q hcp.symm
    simp [hpm, hqm, h1, Nat.gcd_eq_right hqm]
  · have hcp : Nat.Coprime m p := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm |>.symm
    have hcq : Nat.Coprime m q := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqm |>.symm
    simp [hpm, hqm, Nat.Coprime.mul_right hcp hcq]
