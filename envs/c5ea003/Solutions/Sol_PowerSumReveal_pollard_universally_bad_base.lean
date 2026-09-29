-- Prove2me | solution 1 for PowerSumReveal.pollard_universally_bad_base
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:47.81026+00:00
-- url     : https://prove2.me/submissions/a1b13574-c1fa-4015-b94e-cd81827e5390

-- Sol generated from Geometry/PowerSumPollardRobustness.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPollardRobustness
import Theorems.Thm_PowerSumReveal_gcd_prime_eq
import Theorems.Thm_PowerSumReveal_not_dvd_pow_pred_sub_one_of_odd

/-!
# Robustness: the power sum has no "bad base", Pollard's `p-1` does

Pollard's `p-1` method depends on a *base* `a`: it computes `gcd (a^M - 1, N)` and
succeeds only if the multiplicative order of `a` modulo one prime factor divides the
exponent `M` while the order modulo the other one does not.  The power-sum quantity
`powerSum N k = ∑_{a=1}^{N} a^k` has no base parameter at all: it aggregates every
residue simultaneously.

This file makes the contrast precise.

* `PowerSumReveal.pollard_universally_bad_base` — for a semiprime `N = p*q` of distinct
  *odd* primes, the base `a = N - 1` (a nontrivial base, coprime to `N`) is bad for
  **every** exponent `M ≥ 1`: `gcd (a^M - 1, N) ∈ {1, N}`, never a proper factor.
* `PowerSumReveal.powerSum_succeeds_where_pollard_fails` — at the very exponent
  `k = p - 1` where that base makes Pollard return the useless value `N`, the power
  sum returns the factor `q` (under the standard side condition `(q-1) ∤ (p-1)`).
* `PowerSumReveal.pollard_bad_base_example` — the concrete instance `N = 35`, `M = 4`,
  `a = 6`: Pollard returns `35`, the power sum returns `7`.

Note that the statement `a = N - 1` is a genuinely nontrivial base: `1 < N - 1 < N`.
-/

open PowerSumReveal

open Finset

variable {p q : ℕ}


/-- Casting `(N-1)^M - 1` into `ZMod p`. -/
lemma cast_pow_pred_sub_one (r N M : ℕ) [NeZero r] (hN : 2 ≤ N) :
    (((N - 1) ^ M - 1 : ℕ) : ZMod r) = ((N : ZMod r) - 1) ^ M - 1 := by
  have h1 : 1 ≤ (N - 1) ^ M := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h1]
  push_cast [Nat.cast_sub (show 1 ≤ N by omega)]
  ring


/-- For an even exponent `M`, every divisor of `N` divides `(N-1)^M - 1`. -/
lemma dvd_pow_pred_sub_one_of_even {r N M : ℕ} (hr : r.Prime) (hrN : r ∣ N) (hN : 2 ≤ N)
    (hM : Even M) : r ∣ ((N - 1) ^ M - 1) := by
  haveI : Fact r.Prime := ⟨hr⟩
  refine (ZMod.natCast_eq_zero_iff _ r).1 ?_
  rw [cast_pow_pred_sub_one r N M hN, (ZMod.natCast_eq_zero_iff N r).2 hrN, zero_sub,
    hM.neg_one_pow, sub_self]






open PowerSumReveal in
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hp2 : p ≠ 2) (hq2 : q ≠ 2) (M : ℕ) :
    pollardGcd (p * q) (p * q - 1) M = if Even M then p * q else 1 := by
  have hN : 2 ≤ p * q := by
    have := hp.two_le; have := hq.two_le; nlinarith
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hpN : p ∣ p * q := ⟨q, rfl⟩
  have hqN : q ∣ p * q := ⟨p, by ring⟩
  unfold pollardGcd
  rw [Nat.Coprime.gcd_mul _ hcop, gcd_prime_eq hp, gcd_prime_eq hq]
  rcases Nat.even_or_odd M with hM | hM
  · rw [if_pos hM, if_pos (dvd_pow_pred_sub_one_of_even hp hpN hN hM),
      if_pos (dvd_pow_pred_sub_one_of_even hq hqN hN hM)]
  · rw [if_neg (Nat.not_even_iff_odd.2 hM),
      if_neg (not_dvd_pow_pred_sub_one_of_odd hp hp2 hpN hN hM),
      if_neg (not_dvd_pow_pred_sub_one_of_odd hq hq2 hqN hN hM), one_mul]
