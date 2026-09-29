-- Prove2me | solution 1 for Combinatorics.PowerSumReveal.gcd_powerSum_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T01:01:35.630214+00:00
-- url     : https://prove2.me/submissions/2deaeef7-a20e-45a4-9f52-f7a256865c2b

-- Sol generated from Combinatorics/PowerSumFactorReveal.lean
import Mathlib
import Definitions.Def_Combinatorics_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_gcd_powerSum_squarefree

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
theorem solution{N k : ℕ} (hN : 1 < N) (hsq : Squarefree N) (hk : k ≠ 0) :
    Nat.gcd (powerSum N k) N = 1 ↔ lam N ∣ k := by
  classical
  have hN0 : N ≠ 0 := by omega
  rw [gcd_powerSum_squarefree hN0 hsq hk, lam, Finset.lcm_dvd_iff]
  constructor
  · intro h p hp
    by_contra hc
    have hmem : p ∈ N.primeFactors.filter (fun p => ¬ (p - 1) ∣ k) :=
      Finset.mem_filter.mpr ⟨hp, hc⟩
    have hpdvd : p ∣ ∏ p ∈ N.primeFactors.filter (fun p => ¬ (p - 1) ∣ k), p :=
      Finset.dvd_prod_of_mem _ hmem
    rw [h] at hpdvd
    exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp hpdvd)
  · intro h
    refine Finset.prod_eq_one ?_
    intro p hp
    rw [Finset.mem_filter] at hp
    exact absurd (h p hp.1) hp.2
