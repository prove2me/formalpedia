-- Prove2me | solution 1 for PowerSumGCD.gcd_powerSum_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:31:47.306564+00:00
-- url     : https://prove2.me/submissions/69263f1f-3616-429a-8f33-a14d51b62f36

-- Sol generated from Novelty/PowerSumGCDCarmichael.lean
import Mathlib
import Definitions.Def_Novelty_PowerSumGCDCarmichael
import Definitions.Def_Novelty_PowerSumGCDFactoring
import Theorems.Thm_PowerSumGCD_gcd_powerSum_semiprime

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
theorem solution{p q k : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hk : 0 < k) :
    Nat.gcd (powerSum (p * q) k) (p * q) = 1 ↔ carmichael p q ∣ k := by
  rw [gcd_powerSum_semiprime hp hq hpq hk, carmichael, Nat.lcm_dvd_iff]
  constructor
  · intro h
    by_cases h1 : (p - 1) ∣ k <;> by_cases h2 : (q - 1) ∣ k
    · exact ⟨h1, h2⟩
    · rw [if_pos h1, if_neg h2, one_mul] at h; exact absurd h hq.one_lt.ne'
    · rw [if_neg h1, if_pos h2, mul_one] at h; exact absurd h hp.one_lt.ne'
    · rw [if_neg h1, if_neg h2] at h
      exact absurd (Nat.eq_one_of_mul_eq_one_right h) hp.one_lt.ne'
  · rintro ⟨h1, h2⟩
    rw [if_pos h1, if_pos h2, one_mul]
