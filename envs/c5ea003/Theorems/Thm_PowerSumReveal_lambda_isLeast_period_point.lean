-- Prove2me | Theorems.Thm_PowerSumReveal_lambda_isLeast_period_point
-- name    : PowerSumReveal.lambda_isLeast_period_point
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:37:58.483359+00:00
-- url     : https://prove2.me/theorems/af2407e4-7b0a-4c4f-a14e-c9b9386c9879
-- title:
--   Theorem 3c.
-- statement:
--   **Theorem 3c.**  `λ(N)` is the least positive exponent at which the gcd becomes `1`;
--   in particular it is *readable* from the gcd sequence.
--
--   ```lean
--   theorem PowerSumReveal.lambda_isLeast_period_point(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
--       IsLeast {k : ℕ | 0 < k ∧ Nat.gcd (powerSum (p * q) k) (p * q) = 1} (carmichael p q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PowerSumCarmichaelPeriod.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PowerSumCarmichaelPeriod.lean#L90

-- Thm stub generated from Geometry/PowerSumCarmichaelPeriod.lean
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

theorem PowerSumReveal.lambda_isLeast_period_point(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    IsLeast {k : ℕ | 0 < k ∧ Nat.gcd (powerSum (p * q) k) (p * q) = 1} (carmichael p q) := by sorry
