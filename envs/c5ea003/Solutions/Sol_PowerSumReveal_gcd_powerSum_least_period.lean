-- Prove2me | solution 1 for PowerSumReveal.gcd_powerSum_least_period
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:56:44.840508+00:00
-- url     : https://prove2.me/submissions/6c421794-25d0-4c8e-81f1-992eee28dd99

-- Sol generated from Geometry/PowerSumCarmichaelPeriod.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumCarmichaelPeriod
import Definitions.Def_Geometry_PowerSumFactorReveal
import Theorems.Thm_PowerSumReveal_carmichael_pos
import Theorems.Thm_PowerSumReveal_gcd_powerSum_eq_one_iff

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
theorem solution(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d : ℕ}
    (hd0 : 0 < d) (hd : d < carmichael p q) :
    ∃ k : ℕ, 0 < k ∧ Nat.gcd (powerSum (p * q) (k + d)) (p * q)
      ≠ Nat.gcd (powerSum (p * q) k) (p * q) := by
  refine ⟨carmichael p q, carmichael_pos hp hq, ?_⟩
  have hlam : carmichael p q ≠ 0 := (carmichael_pos hp hq).ne'
  have h1 : Nat.gcd (powerSum (p * q) (carmichael p q)) (p * q) = 1 :=
    (gcd_powerSum_eq_one_iff hp hq hpq hlam).2 dvd_rfl
  have h2 : ¬ carmichael p q ∣ (carmichael p q + d) := by
    intro h
    have : carmichael p q ∣ d := (Nat.dvd_add_right dvd_rfl).mp h
    exact absurd (Nat.le_of_dvd hd0 this) (not_le.mpr hd)
  have h3 : Nat.gcd (powerSum (p * q) (carmichael p q + d)) (p * q) ≠ 1 := by
    intro h
    exact h2 ((gcd_powerSum_eq_one_iff hp hq hpq (by omega)).1 h)
  rw [h1]; exact h3
