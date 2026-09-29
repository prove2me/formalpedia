-- Prove2me | Theorems.Thm_QubitTrade_card_goodRecords_eq_euler_product
-- name    : QubitTrade.card_goodRecords_eq_euler_product
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:51:35.961653+00:00
-- url     : https://prove2.me/theorems/18efea64-469a-49f8-981e-e97c1fe8f2d2
-- title:
--   Exact success density (Euler product).
-- statement:
--   **Exact success density (Euler product).**  The number of length-`m` records
--   of numerators in `[0, r)` that recover the order `r` is `r^m ∏_{p ∣ r} (1 - p^{-m})`,
--   i.e. Jordan's totient `J_m(r)`.  Dividing by `r^m`, the success probability of an
--   `m`-sample record is exactly `∏_{p ∣ r} (1 - p^{-m})`.
--
--   ```lean
--   theorem QubitTrade.card_goodRecords_eq_euler_product(hr : 0 < r) :
--       ((goodRecords r m).card : ℚ)
--         = (r : ℚ) ^ m * ∏ p ∈ r.primeFactors, (1 - ((p : ℚ) ^ m)⁻¹) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/JordanCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/JordanCount.lean#L197

-- Thm stub generated from Algebra/QubitTrade/JordanCount.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_JordanCount
import Definitions.Def_Algebra_QubitTrade_SuccessDensity

/-!
# QUBIT-TRADE XII: the exact number of successful records

`SuccessDensity.lean` bounds the number of *good* records — the length-`m`
records of numerators whose joint gcd is coprime to the order `r`, i.e. exactly
the records that `recordEstimate` turns into the true order — from below by
`r^m / 2`.  Here we compute that number **exactly**.

The count is Jordan's totient `J_m(r)`:

* `QubitTrade.sum_card_goodRecords` — the divisor identity
  `∑_{d ∣ r} #good(d, m) = r^m`, proved by an explicit bijection that rescales a
  record by the gcd of its entries with `r`;
* `QubitTrade.card_goodRecords_eq_moebius_sum` — Möbius inversion of that
  identity: `#good(r, m) = ∑_{d ∣ r} μ(d) · (r/d)^m`;
* `QubitTrade.card_goodRecords_eq_euler_product` — the closed Euler product
  `#good(r, m) = r^m · ∏_{p ∣ r} (1 − p^{−m})`.

The last statement is the exact form of the success density conjectured in the
previous cycle: the failure probability of an `m`-sample record is exactly
`1 − ∏_{p ∣ r} (1 − p^{−m})`, which is `≤ ω(r)·2^{−m}` and `< 1/2` for `m ≥ 2`,
recovering the earlier bounds and pinning the constant.
-/

open QubitTrade

open Finset ArithmeticFunction

variable {r m : ℕ}

/-! ## Rescaling records -/









/-! ## The Euler product -/

theorem QubitTrade.card_goodRecords_eq_euler_product(hr : 0 < r) :
    ((goodRecords r m).card : ℚ)
      = (r : ℚ) ^ m * ∏ p ∈ r.primeFactors, (1 - ((p : ℚ) ^ m)⁻¹) := by sorry
