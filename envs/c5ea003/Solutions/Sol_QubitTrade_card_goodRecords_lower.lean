-- Prove2me | solution 1 for QubitTrade.card_goodRecords_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:21:26.687246+00:00
-- url     : https://prove2.me/submissions/454b1171-a961-4d7f-a8d0-b2694b116f69

-- Sol generated from Algebra/QubitTrade/SuccessDensity.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_RecordCount
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Definitions.Def_Algebra_QubitTrade_SuccessDensity
import Theorems.Thm_QubitTrade_card_allRecords
import Theorems.Thm_QubitTrade_pow_mul_card_badRecords_lt

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




theorem card_good_add_card_bad (r m : ℕ) :
    (goodRecords r m).card + (badRecords r m).card = r ^ m := by
  classical
  rw [goodRecords, badRecords, ← card_allRecords (r := r) (m := m)]
  exact Finset.card_filter_add_card_filter_not (p := fun f => Nat.gcd
    (recordGcd (List.ofFn f)) r = 1)








open QubitTrade in
theorem solution(hr : 0 < r) (hm : 2 ≤ m) :
    (2 ^ (m - 1) - 1) * r ^ m < 2 ^ (m - 1) * (goodRecords r m).card := by
  set K := 2 ^ (m - 1) with hK
  have hK1 : 1 ≤ K := Nat.one_le_two_pow
  have hsum := card_good_add_card_bad r m
  have hbad := pow_mul_card_badRecords_lt (r := r) (m := m) hr hm
  rw [← hK] at hbad
  have hdist : K * (goodRecords r m).card + K * (badRecords r m).card = K * r ^ m := by
    rw [← Nat.mul_add, hsum]
  have hNle : r ^ m ≤ K * r ^ m := Nat.le_mul_of_pos_left _ (by omega)
  have hsubeq : (K - 1) * r ^ m = K * r ^ m - r ^ m := by
    rw [Nat.sub_mul, one_mul]
  omega
