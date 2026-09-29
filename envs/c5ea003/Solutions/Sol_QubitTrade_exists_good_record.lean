-- Prove2me | solution 1 for QubitTrade.exists_good_record
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T16:39:18.245128+00:00
-- url     : https://prove2.me/submissions/844563b0-c189-4738-bab0-6ce24316ffb7

-- Sol generated from Algebra/QubitTrade/RecordCount.lean
import Mathlib
import Definitions.Def_Algebra_QubitTrade_RecordCount
import Definitions.Def_Algebra_QubitTrade_SampleFungibility
import Theorems.Thm_QubitTrade_card_allRecords
import Theorems.Thm_QubitTrade_card_bad_records_le

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
theorem solution(hr : 0 < r) (hm : r.primeFactors.card < 2 ^ m) :
    ∃ f : Fin m → ℕ, (∀ i, f i < r) ∧ Nat.gcd (recordGcd (List.ofFn f)) r = 1 := by
  have hlt : (badRecords r m).card < (allRecords r m).card := by
    rw [card_allRecords]
    have h1 := card_bad_records_le (r := r) (m := m) hr
    have hrm : 0 < r ^ m := Nat.pow_pos hr
    by_contra hcon
    push_neg at hcon
    have h3 : r ^ m * 2 ^ m ≤ r.primeFactors.card * r ^ m :=
      le_trans (Nat.mul_le_mul_right _ hcon) h1
    have h5 : r ^ m * 2 ^ m ≤ r ^ m * r.primeFactors.card := by
      calc r ^ m * 2 ^ m ≤ r.primeFactors.card * r ^ m := h3
        _ = r ^ m * r.primeFactors.card := mul_comm _ _
    have h4 := Nat.le_of_mul_le_mul_left h5 hrm
    omega
  obtain ⟨f, hf, hfb⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨f, ?_, ?_⟩
  · intro i
    rw [allRecords, Fintype.mem_piFinset] at hf
    simpa using hf i
  · by_contra hgcd
    exact hfb (by rw [badRecords, Finset.mem_filter]; exact ⟨hf, hgcd⟩)
