-- Prove2me | solution 1 for PowerSumGCD.pow_add_modEq_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:33:14.587547+00:00
-- url     : https://prove2.me/submissions/d1543df5-44d6-4a1c-a75e-70198b3a08dc

-- Sol generated from Novelty/PowerSumGCDCarmichael.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDCarmichael
import Definitions.Def_Novelty_PowerSumGCDFactoring

/-!
# Carmichael periodicity of the power-sum gcd, and the correct factor-recovery identity

Continuing `Novelty.PowerSumGCDFactoring`, let `N = p q` be a semiprime and

  `g(k) = gcd(F(N,k), N)`,  `F(N,k) = ∑_{a=1}^{N} a^k`.

The closed formula `gcd_powerSum_semiprime` shows `g` depends on `k` only through the
two divisibility conditions `(p-1) ∣ k`, `(q-1) ∣ k`.  Consequently `g` is periodic with
period `λ(N) = lcm(p-1, q-1)`, and `λ(N)` is *exactly* the minimal period; indeed

  `g(k) = 1 ↔ λ(N) ∣ k`   (for `k > 0`),

so the Carmichael exponent is readable off the zero set of `g`.

We also prove the stronger, term-wise statement that the power sum itself is periodic
modulo `N` (`powerSum_modEq_add_period`), which is the Korselt/Carmichael congruence
`a^{k+λ} ≡ a^k (mod N)` summed over `a`.

## Critique of the naive recovery formula

The informal claim "`p + q = N - λ(N) + 1`" is **false** whenever `gcd(p-1,q-1) > 1`,
in particular for *every* product of two distinct odd primes.  The correct statement is

  `p + q + λ(N) · gcd(p-1, q-1) = N + 1`   (`sum_primes_recovery`),

and the naive formula always strictly overshoots (`naive_recovery_strict_lt`), with the
explicit witness `N = 15` (`naive_recovery_counterexample`).

## Main results

* `powerSum_modEq_add_period`, `gcd_powerSum_periodic` : periodicity;
* `gcd_powerSum_eq_one_iff` : `g(k) = 1 ↔ λ(N) ∣ k`;
* `period_dvd_of_isPeriod`, `carmichael_is_least_period` : minimality of `λ(N)`;
* `sum_primes_recovery`, `naive_recovery_strict_lt`, `naive_recovery_counterexample`.
-/

open Finset

open PowerSumGCD













open PowerSumGCD in
theorem solution{p a k L : ℕ} (hp : p.Prime) (hk : 0 < k) (hL : (p - 1) ∣ L) :
    a ^ (k + L) ≡ a ^ k [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  push_cast
  obtain ⟨t, rfl⟩ := hL
  by_cases h : (a : ZMod p) = 0
  · rw [h, zero_pow hk.ne', zero_pow (by omega)]
  · rw [pow_add, pow_mul, ZMod.pow_card_sub_one_eq_one h, one_pow, mul_one]
