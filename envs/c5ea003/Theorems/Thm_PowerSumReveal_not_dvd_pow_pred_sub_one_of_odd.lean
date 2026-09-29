-- Prove2me | Theorems.Thm_PowerSumReveal_not_dvd_pow_pred_sub_one_of_odd
-- name    : PowerSumReveal.not_dvd_pow_pred_sub_one_of_odd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:37:34.27508+00:00
-- url     : https://prove2.me/theorems/26e75112-388c-41d6-85b0-2dd155360111
-- title:
--   For an odd prime factor `r` of `N` and an *odd* exponent `M`, the prime `r` does not
-- statement:
--   For an odd prime factor `r` of `N` and an *odd* exponent `M`, the prime `r` does not
--   divide `(N-1)^M - 1`, because that quantity is `≡ -2 (mod r)`.
--
--   ```lean
--   theorem PowerSumReveal.not_dvd_pow_pred_sub_one_of_odd{r N M : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
--       (hrN : r ∣ N) (hN : 2 ≤ N) (hM : Odd M) :
--       ¬ r ∣ ((N - 1) ^ M - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PowerSumPollardRobustness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PowerSumPollardRobustness.lean#L42

-- Thm stub generated from Geometry/PowerSumPollardRobustness.lean
import Mathlib
import Definitions.Def_Geometry_PowerSumFactorReveal
import Definitions.Def_Geometry_PowerSumPollardRobustness

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

theorem PowerSumReveal.not_dvd_pow_pred_sub_one_of_odd{r N M : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrN : r ∣ N) (hN : 2 ≤ N) (hM : Odd M) :
    ¬ r ∣ ((N - 1) ^ M - 1) := by sorry
