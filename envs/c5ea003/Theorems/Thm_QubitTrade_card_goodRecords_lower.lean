-- Prove2me | Theorems.Thm_QubitTrade_card_goodRecords_lower
-- name    : QubitTrade.card_goodRecords_lower
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:51:22.252292+00:00
-- url     : https://prove2.me/theorems/7dafac56-341e-40b8-840f-30b33d44fce8
-- title:
--   Exponential concentration of the sample side of the ledger.
-- statement:
--   **Exponential concentration of the sample side of the ledger.**  For every
--   order `r ≥ 1` and every `m ≥ 2`, the good records outnumber `r^m (1 − 2^{-(m-1)})`:
--   the success probability of `m` samples is `> 1 − 2^{-(m-1)}`, uniformly in `r`.
--   This is the sharp form of `RecordCount.good_record_of_log_log`, with the `ω(r)`
--   factor of the earlier union bound removed.
--
--   ```lean
--   theorem QubitTrade.card_goodRecords_lower(hr : 0 < r) (hm : 2 ≤ m) :
--       (2 ^ (m - 1) - 1) * r ^ m < 2 ^ (m - 1) * (goodRecords r m).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/QubitTrade/SuccessDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/QubitTrade/SuccessDensity.lean#L322

-- Thm stub generated from Algebra/QubitTrade/SuccessDensity.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_RecordCount
import Definitions.Def_Algebra_QubitTrade_SuccessDensity

/-!
# QUBIT-TRADE X: two samples already succeed on a majority of records

`RecordCount.lean` shows that a *good* record — one whose numerators are jointly
coprime to the order `r` — exists as soon as `ω(r) < 2^m`.  That is an existence
statement; it says nothing about how likely a random record is to be good, and
the union bound used there is lossy by a factor `ω(r)`.

Here we sharpen the count to a **density** statement, and the loss disappears:

* `QubitTrade.sum_inv_sq_primes_lt_half` — for *every* finite set `S` of primes,
  `Σ_{p ∈ S} p⁻² < 1/2`.  This is an unconditional, elementary bound: the four
  primes below `11` contribute `18589/44100`, and the remaining primes, being
  distinct odd numbers `≥ 11`, contribute at most `1/20` by telescoping
  `(2k+1)⁻² ≤ (4k)⁻¹ − (4(k+1))⁻¹`.
* `QubitTrade.card_badRecords_le_sum` — the exact union bound
  `#bad ≤ Σ_{p ∣ r} (r/p)^m`, with no `ω(r)` slack.
* `QubitTrade.two_pow_card_goodRecords` — hence for **every** `r ≥ 1` and every
  `m ≥ 2`, `r^m < 2 · #good`: *strictly more than half* of all length-`m`
  records of numerators recover the order.
* `QubitTrade.two_samples_recover_majority` — the same statement phrased through
  the estimator `recordEstimate` of `SampleFungibility.lean`: two samples read
  above the register threshold return the true order `r` for a majority of
  numerator pairs, uniformly in `r`.
* `QubitTrade.pow_mul_card_badRecords_lt` / `QubitTrade.card_goodRecords_lower` —
  the concentration form: the failure probability of `m ≥ 2` samples is
  `< 2^{-(m-1)}`, again with no `ω(r)` factor, so the success probability rises
  exponentially in the sample count while remaining uniform in the order.

This settles, with the explicit constant `1/2` in place of the conjectured
`6/π² ≈ 0.6079`, the quantitative half of the "qubit ↔ sample" ledger: above the
`2 log₂ r` register threshold, **two** samples suffice with probability `> 1/2`
for every order, so the sample budget really is `O(1)` per constant success
probability, while the qubit budget is rigid.
-/

open QubitTrade

open Finset

/-! ### An unconditional bound on `Σ_p p⁻²` over primes -/






/-! ### From the prime bound to the density of good records -/

variable {r m : ℕ}

theorem QubitTrade.card_goodRecords_lower(hr : 0 < r) (hm : 2 ≤ m) :
    (2 ^ (m - 1) - 1) * r ^ m < 2 ^ (m - 1) * (goodRecords r m).card := by sorry
