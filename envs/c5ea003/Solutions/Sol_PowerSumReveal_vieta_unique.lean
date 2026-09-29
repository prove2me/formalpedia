-- Prove2me | solution 1 for PowerSumReveal.vieta_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:49.023977+00:00
-- url     : https://prove2.me/submissions/54737f33-be32-4a98-9017-b465e905f98a

-- Sol generated from Geometry/PowerSumCarmichaelPeriod.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumCarmichaelPeriod
import Definitions.Def_Geometry_PowerSumFactorReveal

/-!
# Carmichael periodicity of the power-sum gcd, and factor recovery

Continuing `Geometry.PowerSumFactorReveal`, let `N = p * q` be a semiprime and

`g k = gcd (powerSum N k) N`,  `powerSum N k = ∑_{a=1}^{N} a^k`.

The master formula of the previous file shows that, for `k ≥ 1`, `g k` depends on `k`
only through the two Boolean quantities `(p-1) ∣ k` and `(q-1) ∣ k`.  Hence `g` is
periodic with period the Carmichael number `λ(N) = lcm (p-1) (q-1)`, and in fact
`λ(N)` is *exactly* the least period, because

`g k = 1 ↔ λ(N) ∣ k`   (for `k ≥ 1`).

So `λ(N)` is readable off the sequence `g 1, g 2, g 3, …` as the position of its first
`1`.  The last section addresses **factor recovery**.  The naive claim
"`p + q = N - λ(N) + 1`" is *false* in general — it confuses `λ(N) = lcm(p-1,q-1)`
with `φ(N) = (p-1)(q-1)`; `p = 5, q = 13` is a counterexample
(`lambda_recovery_counterexample`).  The correct identity is

`gcd (p-1) (q-1) * λ(N) + (p + q) = N + 1`,

which reduces to the naive one exactly under the guard `gcd (p-1) (q-1) = 1`.
Together with a Vieta uniqueness lemma this recovers `p` and `q`.

## Main results

* `PowerSumReveal.gcd_powerSum_periodic` — periodicity with period `λ(N)`.
* `PowerSumReveal.gcd_powerSum_eq_one_iff` — `g k = 1 ↔ λ(N) ∣ k`.
* `PowerSumReveal.lambda_isLeast_period_point` — `λ(N)` is the least `k ≥ 1` with `g k = 1`.
* `PowerSumReveal.gcd_powerSum_least_period` — no smaller positive number is a period.
* `PowerSumReveal.lambda_recovery_counterexample` — the naive recovery formula fails.
* `PowerSumReveal.carmichael_totient_recovery` — the corrected recovery identity.
* `PowerSumReveal.semiprime_recovered_from_period` — full recovery of `{p, q}` under the guard.
-/

open PowerSumReveal

open Finset

variable {p q : ℕ}





/-! ## Periodicity -/





/-! ## Factor recovery: the naive formula and its repair -/







open PowerSumReveal in
theorem solution{s N a b a' b' : ℕ} (h1 : a + b = s) (h2 : a * b = N)
    (h3 : a' + b' = s) (h4 : a' * b' = N) (hab : a ≤ b) (hab' : a' ≤ b') :
    a = a' ∧ b = b' := by
  have key : ((a : ℤ) - a') * ((a : ℤ) + a' - s) = 0 := by
    have e1 : (a : ℤ) * ((s : ℤ) - a) = N := by
      have : (b : ℤ) = (s : ℤ) - a := by push_cast [← h1]; ring
      rw [← this]; exact_mod_cast h2
    have e2 : (a' : ℤ) * ((s : ℤ) - a') = N := by
      have : (b' : ℤ) = (s : ℤ) - a' := by push_cast [← h3]; ring
      rw [← this]; exact_mod_cast h4
    nlinarith [e1, e2]
  rcases mul_eq_zero.1 key with h | h
  · have : a = a' := by omega
    exact ⟨this, by omega⟩
  · -- here `a' = b`, hence `b' = a`, and the orderings force `a = b`
    have hab2 : (a : ℤ) + a' = s := by omega
    have ha' : a' = b := by omega
    have hb' : b' = a := by omega
    subst ha'; subst hb'
    omega
