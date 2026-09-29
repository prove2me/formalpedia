-- Prove2me | Theorems.Thm_PowerSumReveal_gcd_powerSum_eq_self_iff
-- name    : PowerSumReveal.gcd_powerSum_eq_self_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:36:46.779398+00:00
-- url     : https://prove2.me/theorems/8e055451-5083-419a-84d0-6d2c208dae41
-- title:
--   The gcd is the whole modulus exactly when neither `p-1` nor `q-1` divides `k`.
-- statement:
--   The gcd is the whole modulus exactly when neither `p-1` nor `q-1` divides `k`.
--
--   ```lean
--   theorem PowerSumReveal.gcd_powerSum_eq_self_iff(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {k : ℕ}
--       (hk : k ≠ 0) :
--       Nat.gcd (powerSum (p * q) k) (p * q) = p * q ↔ (¬ (p - 1) ∣ k ∧ ¬ (q - 1) ∣ k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PowerSumFirstHit.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PowerSumFirstHit.lean#L40

-- Thm stub generated from Geometry/PowerSumFirstHit.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumCarmichaelPeriod
import Definitions.Def_Geometry_PowerSumFactorReveal

/-!
# Cycle 2: the first hit, an unconditional reveal, and the density of good exponents

The master formula of `Geometry.PowerSumFactorReveal` says that, for `N = p*q` with
`p ≠ q` prime and `k ≥ 1`,

`gcd (powerSum N k) N = (if (p-1) ∣ k then 1 else p) * (if (q-1) ∣ k then 1 else q)`.

Three consequences are proved here.

* **Unconditional reveal.**  If `p < q` then the side condition `(q-1) ∤ (p-1)` of
  Theorem 1 is *automatic*, so `gcd (powerSum N (p-1)) N = q` with no extra hypothesis.
  (This strengthens the original statement of Theorem 1.)
* **First hit.**  The least exponent `k ≥ 1` at which the gcd is not the trivial value
  `N` is exactly `k* = min (p-1) (q-1)`, and `(k*+1)^2 ≤ N`, i.e. `k* < √N`.
  At `k = k*` the gcd is already a *proper* factor.
* **Density of good exponents.**  Inside one Carmichael period `λ = lcm (p-1) (q-1)`
  the number of exponents that reveal a proper factor is exactly
  `λ/(p-1) + λ/(q-1) - 2`.  So the useful exponents are a `(1/(p-1) + 1/(q-1))`-fraction
  of the period: sparse, which is the quantitative form of the "period-finding barrier".

## Main results

* `PowerSumReveal.gcd_powerSum_eq_self_iff`
* `PowerSumReveal.powerSum_factor_reveal_of_lt` — unconditional Theorem 1.
* `PowerSumReveal.first_hit_isLeast` — first hit at `min (p-1) (q-1)`.
* `PowerSumReveal.first_hit_sq_le` — `k* < √N`.
* `PowerSumReveal.card_revealing_exponents` — density inside one period.
-/

open PowerSumReveal

open Finset

variable {p q : ℕ}

/-! ## A value table for the gcd -/

theorem PowerSumReveal.gcd_powerSum_eq_self_iff(hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {k : ℕ}
    (hk : k ≠ 0) :
    Nat.gcd (powerSum (p * q) k) (p * q) = p * q ↔ (¬ (p - 1) ∣ k ∧ ¬ (q - 1) ∣ k) := by sorry
