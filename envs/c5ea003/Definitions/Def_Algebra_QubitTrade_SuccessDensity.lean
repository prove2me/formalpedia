-- Prove2me | Definitions.Def_Algebra_QubitTrade_SuccessDensity
-- name    : Algebra_QubitTrade_SuccessDensity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T09:08:59.951712+00:00
-- url     : https://prove2.me/theorems/3ab42b22-d557-4c5d-944e-f9e2295f5f88
-- title:
--   Aether Catalog definitions — Algebra_QubitTrade_SuccessDensity
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.QubitTrade.SuccessDensity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/QubitTrade/SuccessDensity.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_QubitTrade_RecordCount
import Definitions.Def_Algebra_QubitTrade_SampleFungibility

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

namespace QubitTrade

open Finset

/-! ### An unconditional bound on `Σ_p p⁻²` over primes -/






/-! ### From the prime bound to the density of good records -/

variable {r m : ℕ}



/-- The records that *do* satisfy the joint-coprimality criterion. -/
noncomputable def goodRecords (r m : ℕ) : Finset (Fin m → ℕ) :=
  (allRecords r m).filter (fun f => Nat.gcd (recordGcd (List.ofFn f)) r = 1)








end QubitTrade


