-- Prove2me | solution 1 for QubitTrade.card_bad_records_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:17:00.241425+00:00
-- url     : https://prove2.me/submissions/d5c5ce21-69ff-4544-894e-5f144538e3c3

-- Sol generated from Algebra/QubitTrade/RecordCount.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_RecordCount
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Theorems.Thm_QubitTrade_badRecords_subset
import Theorems.Thm_QubitTrade_card_multipleRecords

/-!
# QUBIT-TRADE IX: how many samples? `log₂ log₂ r` of them

Above the resolution threshold the only obstruction left is `gcd (k, r) > 1`, and
`SampleFungibility.lean` says a record works exactly when its numerators are
jointly coprime to `r`.  Here we *count* the bad records and get the second half
of the resource ledger:

* `QubitTrade.card_bad_records_le` — the number of length-`m` records of
  numerators that fail the joint-coprimality test is at most
  `ω(r) · r^m / 2^m` (stated multiplicatively, in `ℕ`);
* `QubitTrade.exists_good_record` — hence a *successful* record of length `m`
  exists as soon as `ω(r) < 2^m`;
* `QubitTrade.good_record_of_log_log` — and `m = log₂ log₂ r + 1` samples always
  suffice, since `ω(r) ≤ log₂ r`.

Together with `Threshold.lean`: **`2 log₂ r` qubits and `log₂ log₂ r` samples.**
The register size is forced; the sample count is almost free.  That asymmetry is
the precise sense in which qubits and samples are *not* fungible below the
threshold and only mildly fungible above it.
-/

open QubitTrade

open Finset

variable {r m : ℕ}













open QubitTrade in
theorem solution(hr : 0 < r) :
    (badRecords r m).card * 2 ^ m ≤ r.primeFactors.card * r ^ m := by
  have hsub := Finset.card_le_card (badRecords_subset (m := m) hr)
  have hbi : ((r.primeFactors).biUnion (fun p => multipleRecords r m p)).card
      ≤ ∑ p ∈ r.primeFactors, (multipleRecords r m p).card := Finset.card_biUnion_le
  have hterm : ∀ p ∈ r.primeFactors, (multipleRecords r m p).card * 2 ^ m ≤ r ^ m := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ r := Nat.dvd_of_mem_primeFactors hp
    rw [card_multipleRecords hprime.pos hpd, ← mul_pow]
    refine Nat.pow_le_pow_left ?_ m
    have h2 : 2 ≤ p := hprime.two_le
    have : r / p * p ≤ r := Nat.div_mul_le_self r p
    calc r / p * 2 ≤ r / p * p := Nat.mul_le_mul_left _ h2
      _ ≤ r := this
  calc (badRecords r m).card * 2 ^ m
      ≤ (∑ p ∈ r.primeFactors, (multipleRecords r m p).card) * 2 ^ m := by
        exact Nat.mul_le_mul_right _ (le_trans hsub hbi)
    _ = ∑ p ∈ r.primeFactors, (multipleRecords r m p).card * 2 ^ m := by
        rw [Finset.sum_mul]
    _ ≤ ∑ _p ∈ r.primeFactors, r ^ m := Finset.sum_le_sum hterm
    _ = r.primeFactors.card * r ^ m := by rw [Finset.sum_const, smul_eq_mul]
