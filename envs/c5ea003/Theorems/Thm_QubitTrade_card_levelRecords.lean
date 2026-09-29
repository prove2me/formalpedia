-- Prove2me | Theorems.Thm_QubitTrade_card_levelRecords
-- name    : QubitTrade.card_levelRecords
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:51:26.60536+00:00
-- url     : https://prove2.me/theorems/39b30372-86fc-4bc0-a109-c4efb8ebf8e4
-- title:
--   Card levelRecords
-- statement:
--   Formal statement of `QubitTrade.card_levelRecords` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem QubitTrade.card_levelRecords{n e : ℕ} (hn : 0 < n) (he : e ∣ n) :
--       (levelRecords n m e).card = (goodRecords (n / e) m).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/JordanCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/JordanCount.lean#L88

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

theorem QubitTrade.card_levelRecords{n e : ℕ} (hn : 0 < n) (he : e ∣ n) :
    (levelRecords n m e).card = (goodRecords (n / e) m).card := by sorry
