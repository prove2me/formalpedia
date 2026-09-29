-- Prove2me | Theorems.Thm_PowerSumGCD_pow_add_modEq_prime
-- name    : PowerSumGCD.pow_add_modEq_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:21:43.133991+00:00
-- url     : https://prove2.me/theorems/382488c3-0cfc-408c-af24-6d7c7dc9186e
-- title:
--   A prime power congruence: for `k > 0` and `(p-1) ∣ L`, raising to the extra exponent
-- statement:
--   A prime power congruence: for `k > 0` and `(p-1) ∣ L`, raising to the extra exponent
--   `L` changes nothing modulo `p`.  Both the unit classes (Fermat) and the zero class
--   (where `k > 0` is what is needed) are covered.
--
--   ```lean
--   theorem PowerSumGCD.pow_add_modEq_prime{p a k L : ℕ} (hp : p.Prime) (hk : 0 < k) (hL : (p - 1) ∣ L) :
--       a ^ (k + L) ≡ a ^ k [MOD p] := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/PowerSumGCDCarmichael.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/PowerSumGCDCarmichael.lean#L52

-- Thm stub generated from Novelty/PowerSumGCDCarmichael.lean
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

theorem PowerSumGCD.pow_add_modEq_prime{p a k L : ℕ} (hp : p.Prime) (hk : 0 < k) (hL : (p - 1) ∣ L) :
    a ^ (k + L) ≡ a ^ k [MOD p] := by sorry
