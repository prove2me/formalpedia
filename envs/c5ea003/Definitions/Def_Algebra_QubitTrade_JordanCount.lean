-- Prove2me | Definitions.Def_Algebra_QubitTrade_JordanCount
-- name    : Algebra_QubitTrade_JordanCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T09:15:45.568721+00:00
-- url     : https://prove2.me/theorems/4745595f-a18e-4582-8bd1-cb392827b8d8
-- title:
--   Aether Catalog definitions — Algebra_QubitTrade_JordanCount
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.QubitTrade.JordanCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/QubitTrade/JordanCount.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_QubitTrade_RecordCount
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
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

namespace QubitTrade

open Finset ArithmeticFunction

variable {r m : ℕ}

/-! ## Rescaling records -/



/-- The records of `allRecords n m` whose gcd meets `n` in exactly `e`. -/
noncomputable def levelRecords (n m e : ℕ) : Finset (Fin m → ℕ) :=
  (allRecords n m).filter (fun f => Nat.gcd (recordGcd (List.ofFn f)) n = e)






/-! ## The Euler product -/



end QubitTrade


